use core::fmt;
use std::{
    collections::HashMap,
    fmt::Display,
    io::{self, Write, stdout},
};

use tracing::trace;

use crate::{
    expression::{BinaryOp, Expr, UnaryOp},
    tokenizer::Token,
};

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Variable {
    value: Option<Expr>,
    mutable: bool,
    var_type: Option<Type>,
}

impl Variable {
    fn new_mutable(value: Option<Expr>) -> Option<Self> {
        Some(Self {
            value,
            var_type: None,
            mutable: true,
        })
    }

    fn new_mutable_typed(value: Option<Expr>, var_type: Type) -> Result<Self, String> {
        if let Some(value) = &value {
            let new_type = Type::expr_type(&value)
                .ok_or_else(|| format!("Cannot infer type of {:?}", value))?;
            if var_type != new_type {
                return Err(format!("Expected type {:?}, got {:?}", var_type, new_type));
            }
        }
        Ok(Self {
            value,
            var_type: Some(var_type),
            mutable: true,
        })
    }

    fn set_value(&mut self, value: Expr) -> Result<Expr, String> {
        if let Some(var_type) = &self.var_type {
            let new_type = Type::expr_type(&value).ok_or("Cannot infer type")?;
            if var_type != &new_type {
                return Err(format!("Expected type {:?}, got {:?}", var_type, new_type));
            }
        }
        self.value = Some(value.clone());
        Ok(value)
    }

    fn get_value(&self) -> Option<Expr> {
        self.value.clone()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Type {
    Int,
    String,
    Bool,
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Type {
    fn expr_type(expr: &Expr) -> Option<Type> {
        match expr {
            Expr::NumLit(_) => Some(Type::Int),
            Expr::StringLit(_) => Some(Type::String),
            Expr::BoolLit(_) => Some(Type::Bool),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Function {
    args: Vec<(String, Option<Type>)>,
    body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Context {
    vars: Vec<HashMap<String, Variable>>,
    functions: HashMap<String, Function>,
    types: HashMap<String, Type>,
    stdout: Vec<String>,
}

impl Context {
    pub(crate) fn new() -> Self {
        let mut types = HashMap::new();
        for (name, type_) in Self::DEFAULT_TYPES {
            types.insert(name.to_string(), type_.clone());
        }
        Self {
            vars: vec![HashMap::new()],
            functions: HashMap::new(),
            types,
            stdout: Vec::new(),
        }
    }

    pub(crate) fn get_var_value(&self, name: &str) -> Option<Expr> {
        self.get_var(name).map(|v| v.get_value())?
    }

    pub(crate) fn get_var(&self, name: &str) -> Option<&Variable> {
        self.vars.iter().rev().find_map(|vars| vars.get(name))
    }

    pub(crate) fn get_var_mut(&mut self, name: &str) -> Option<&mut Variable> {
        self.vars
            .iter_mut()
            .rev()
            .find_map(|vars| vars.get_mut(name))
    }

    pub(crate) fn set_var(
        &mut self,
        name: &String,
        value: Expr,
        var_type: Option<String>,
    ) -> Result<Expr, String> {
        let new_var_type = match var_type {
            Some(var_type) => Some(
                self.types
                    .get(&var_type)
                    .ok_or(format!("Invalid type: {}", var_type))?
                    .clone(),
            ),
            None => None,
        };

        if let Some(var) = self.get_var_mut(name) {
            trace!("Set variable({}) to {:?}", name, value);
            if !var.mutable {
                return Err(format!("Cannot mutate immutable variable: {}", name));
            }
            if let Some(var_type) = new_var_type {
                if Some(var_type) != var.var_type {
                    return Err(format!(
                        "Cannot reassign variable({}) to {:?} (invalid type?)",
                        name, value
                    ));
                }
            }
            var.set_value(value)
        } else {
            trace!("Set new variable({}) to {:?}", name, value);
            let var = match new_var_type {
                Some(var_type) => {
                    Variable::new_mutable_typed(Some(value.clone()), var_type.clone())?
                }
                None => Variable::new_mutable(Some(value.clone())).ok_or(format!(
                    "Cannot set variable({}) to {:?} (invalid type?)",
                    name, value
                ))?,
            };
            self.vars.last_mut().unwrap().insert(name.to_string(), var);
            Ok(value)
        }
    }

    pub(crate) fn flush_stdout(&mut self) -> io::Result<()> {
        if self.stdout.len() == 0 {
            return Ok(());
        }
        let mut l = stdout().lock();
        for s in self.stdout.drain(..) {
            l.write_all(s.as_bytes())?
        }
        println!();
        Ok(())
    }

    const DEFAULT_TYPES: [(&'static str, Type); 4] = [
        ("int", Type::Int),
        ("string", Type::String),
        ("bool", Type::Bool),
        ("drip", Type::Int),
    ];
}

pub(crate) fn interpret(c: &mut Context, expr: Expr) -> Result<Expr, String> {
    trace!("Interpreting: {:?}, context: {:?}", expr, c);
    match expr {
        Expr::Unary(op, a) => match op {
            UnaryOp::Plus => interpret(c, *a),
            UnaryOp::Minus => binary_num_op(c, i32::saturating_sub, Expr::NumLit(0), *a),
            UnaryOp::Negate => negate(c, *a),
        },
        Expr::Binary(op, a, b) => match op {
            BinaryOp::Add => binary_num_op(c, i32::saturating_add, *a, *b),
            BinaryOp::Sub => binary_num_op(c, i32::saturating_sub, *a, *b),
            BinaryOp::Mult => binary_num_op(c, i32::saturating_mul, *a, *b),
            BinaryOp::Div => binary_num_op(c, i32::saturating_div, *a, *b),
            BinaryOp::GreaterThan => binary_comp_op(c, i32::gt, *a, *b),
            BinaryOp::GreaterOrEqualThan => binary_comp_op(c, i32::ge, *a, *b),
            BinaryOp::LessThan => binary_comp_op(c, i32::lt, *a, *b),
            BinaryOp::LessOrEqualThan => binary_comp_op(c, i32::le, *a, *b),
            BinaryOp::Equal => binary_comp_op(c, i32::eq, *a, *b),
        },
        Expr::FunctionCall(Token::Ident(fn_name), args) => {
            interpret_function_call(c, &fn_name, args)
        }
        Expr::FunctionDeclaration(name, args, body) => {
            interpret_function_declaration(c, &name, args, *body)
        }
        Expr::Block(expressions) => {
            let mut last = Expr::NoOp;
            c.vars.push(HashMap::new());
            for expr in expressions {
                last = interpret(c, expr.into())?;
            }
            c.vars.pop();
            Ok(last)
        }
        Expr::NumLit(_) | Expr::StringLit(_) | Expr::BoolLit(_) => Ok(expr),
        Expr::Identifier(var_name) => interpret_identifier(c, var_name),
        Expr::Assignment(var_name, value, var_type) => {
            interpret_assignment(c, var_name, *value, var_type)
        }
        Expr::If(cond, then, else_) => interpret_if(c, *cond, *then, else_.map(|e| *e)),
        Expr::While(cond, body) => interpet_while(c, *cond, *body),
        expr => unimplemented!("{:?}", expr),
    }
}

fn negate(c: &mut Context, expr: Expr) -> Result<Expr, String> {
    let lit = expect_boollit(c, expr)?;
    Ok(Expr::BoolLit(!lit))
}

fn interpet_while(c: &mut Context, cond: Expr, body: Expr) -> Result<Expr, String> {
    let mut res = Expr::NoOp;
    trace!("Interpreting while: {:?}, body: {:?}", cond, body);
    loop {
        let cond = expect_boollit(c, cond.clone())?;
        if !cond {
            break;
        }
        res = interpret(c, body.clone())?;
    }
    trace!("Exiting while loop, result: {:?}", res);
    Ok(res)
}

fn interpret_if(
    c: &mut Context,
    cond: Expr,
    then: Expr,
    else_: Option<Expr>,
) -> Result<Expr, String> {
    let cond = expect_boollit(c, cond)?;
    trace!(
        "Interpreting if: {:?}, then: {:?}, else: {:?}",
        cond, then, else_
    );
    if cond {
        interpret(c, then)
    } else {
        if let Some(else_) = else_ {
            interpret(c, else_)
        } else {
            Ok(Expr::NoOp)
        }
    }
}

fn interpret_identifier(c: &mut Context, var_name: String) -> Result<Expr, String> {
    let v = c
        .get_var_value(&var_name)
        .ok_or(format!("variable({}) not set", var_name))?;
    expect_literal(c, v)
}

fn interpret_assignment(
    c: &mut Context,
    var_name: String,
    value: Expr,
    var_type: Option<String>,
) -> Result<Expr, String> {
    let lit = expect_literal(c, value)?;
    c.set_var(&var_name, lit, var_type)
}

fn interpret_function_call(c: &mut Context, name: &str, args: Vec<Expr>) -> Result<Expr, String> {
    match name {
        "yap" => yap(c, args.get(0).ok_or("Expected an argument")?),
        "vibe" => vibe(c, args.get(0).ok_or("Expected an argument")?),
        fn_name => {
            let func = c
                .functions
                .get(fn_name)
                .ok_or(format!("Function({}) not found", fn_name))?
                .clone();
            if func.args.len() != args.len() {
                return Err(format!(
                    "Expected {} arguments, got {}",
                    func.args.len(),
                    args.len()
                ));
            }

            // create a new scope for the function
            let mut vars = HashMap::new();
            for (i, (arg_name, arg_type)) in func.args.iter().enumerate() {
                let arg = args.get(i).ok_or("Expected an argument")?;
                let arg = expect_literal(c, arg.clone())?;
                let var = match arg_type {
                    Some(arg_type) => Variable::new_mutable_typed(Some(arg), arg_type.clone())?,
                    None => Variable::new_mutable(Some(arg)).unwrap(),
                };
                vars.insert(arg_name.clone(), var);
            }
            c.vars.push(vars);
            trace!("Interpreting function({}) with args: {:?}", name, args);
            let res = interpret(c, func.body.clone())?;
            c.vars.pop();
            Ok(res)
        }
    }
}

fn interpret_function_declaration(
    c: &mut Context,
    name: &str,
    args: Vec<(String, Option<String>)>,
    body: Expr,
) -> Result<Expr, String> {
    let args = args
        .into_iter()
        .map(|(name, var_type)| {
            (
                name,
                var_type.map(|t| {
                    c.types
                        .get(&t)
                        .expect(format!("Invalid type: {}", t).as_str())
                        .clone()
                }),
            )
        })
        .collect();
    c.functions
        .insert(name.to_string(), Function { args, body });
    Ok(Expr::NoOp)
}

fn expect_numlit(c: &mut Context, expr: Expr) -> Result<Expr, String> {
    match expr {
        Expr::NumLit(_) => Ok(expr),
        _ => interpret(c, expr),
    }
}

fn expect_boollit(c: &mut Context, expr: Expr) -> Result<bool, String> {
    match expr {
        Expr::BoolLit(b) => Ok(b),
        _ => match interpret(c, expr) {
            Ok(Expr::BoolLit(b)) => Ok(b),
            Ok(expr) => Err(format!("Expected a boolean, got {:?}", expr)),
            Err(err) => Err(err),
        },
    }
}

fn expect_literal(c: &mut Context, expr: Expr) -> Result<Expr, String> {
    match expr {
        Expr::NumLit(_) | Expr::StringLit(_) | Expr::BoolLit(_) => Ok(expr),
        _ => interpret(c, expr),
    }
}

/// Prints the argument to the stdout
fn yap(c: &mut Context, p1: &Expr) -> Result<Expr, String> {
    let arg = expect_literal(c, p1.clone())?;
    let s = match arg {
        Expr::NumLit(a) => a.to_string(),
        Expr::StringLit(s) => s,
        _ => {
            return Err(format!(
                "Invalid argument, expected number or string, got {:?}",
                arg
            ));
        }
    };
    c.stdout.push(s.to_string());
    Ok(Expr::NoOp)
}

/// Returns the argument's type as string
fn vibe(c: &mut Context, p1: &Expr) -> Result<Expr, String> {
    let arg = expect_literal(c, p1.clone())?;
    match p1 {
        Expr::Identifier(name) => {
            let var = c
                .get_var(name)
                .ok_or(format!("Variable({}) not found", name))?;
            Ok(Expr::StringLit(
                var.var_type
                    .as_ref()
                    .map(|t| t.to_string())
                    .unwrap_or("vibeless".to_string()),
            ))
        }
        Expr::NumLit(_) | Expr::StringLit(_) | Expr::BoolLit(_) => {
            Ok(Expr::StringLit(Type::expr_type(&arg).unwrap().to_string()))
        }
        _ => unimplemented!(),
    }
}

fn binary_num_op(
    c: &mut Context,
    op_fn: impl Fn(i32, i32) -> i32,
    a: Expr,
    b: Expr,
) -> Result<Expr, String> {
    let a = expect_literal(c, a)?;
    let b = expect_literal(c, b)?;
    match (&a, &b) {
        (Expr::NumLit(a), Expr::NumLit(b)) => Ok(Expr::NumLit(op_fn(*a, *b)).into()),
        (Expr::NumLit(a), Expr::StringLit(b)) => {
            Ok(Expr::StringLit(b.to_string() + &a.to_string()).into())
        }
        (Expr::StringLit(a), Expr::NumLit(b)) => {
            Ok(Expr::StringLit(a.to_string() + &b.to_string()).into())
        }
        (Expr::StringLit(a), Expr::StringLit(b)) => {
            Ok(Expr::StringLit(a.to_string() + &b.to_string()).into())
        }
        _ => Err(format!(
            "Invalid operation, expected numbers, got {:?}",
            (a, b)
        )),
    }
}

fn binary_comp_op(
    c: &mut Context,
    op_fn: impl Fn(&i32, &i32) -> bool,
    a: Expr,
    b: Expr,
) -> Result<Expr, String> {
    let a = expect_numlit(c, a)?;
    let b = expect_numlit(c, b)?;
    if let (Expr::NumLit(a), Expr::NumLit(b)) = (&a, &b) {
        return Ok(Expr::BoolLit(op_fn(a, b)).into());
    }
    Err(format!(
        "Invalid comparison, expected numbers, got {:?}",
        (a, b)
    ))
}

#[cfg(test)]
mod tests {
    use crate::expression::helpers::{
        self, binary, block, bool_lit, function, iden, num_lit, string_lit, unary, while_expr,
    };
    use crate::expression::{BinaryOp, UnaryOp};
    use crate::tokenizer::Token;

    use super::*;

    #[test]
    fn add() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(&mut c, binary(BinaryOp::Add, num_lit(1), num_lit(2)))?;
        assert_eq!(res, num_lit(3));
        Ok(())
    }

    #[test]
    fn assignment() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(&mut c, helpers::assignment("a".to_string(), num_lit(1)))?;
        assert_eq!(res, num_lit(1));
        Ok(())
    }

    #[test]
    fn test_interpret_block() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            block(&[
                helpers::assignment("a".to_string(), num_lit(1)),
                helpers::assignment("b".to_string(), num_lit(2)),
                binary(BinaryOp::Add, iden("a"), iden("b")),
            ]),
        )?;
        assert_eq!(res, num_lit(3));
        Ok(())
    }

    #[test]
    fn yap() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            function(
                Token::Ident("yap".to_string()),
                vec![string_lit("hello".to_string())],
            ),
        )?;
        assert_eq!(res, helpers::no_op());
        assert_eq!(c.stdout, vec!["hello".to_string()]);
        Ok(())
    }

    #[test]
    fn test_chained_assignment() -> Result<(), String> {
        let mut c = Context::new();
        // a=b=1
        let res = interpret(
            &mut c,
            helpers::assignment(
                "a".to_string(),
                helpers::assignment("b".to_string(), num_lit(1)),
            ),
        )?;
        assert_eq!(res, num_lit(1));
        assert_eq!(c.get_var_value("a"), Some(num_lit(1)));
        assert_eq!(c.get_var_value("b"), Some(num_lit(1)));
        Ok(())
    }

    #[test]
    fn if_expr() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(&mut c, helpers::if_expr(bool_lit(true), num_lit(1), None))?;
        assert_eq!(res, num_lit(1));
        Ok(())
    }

    #[test]
    fn if_else_expr() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            helpers::if_expr(bool_lit(false), num_lit(1), Some(num_lit(2))),
        )?;
        assert_eq!(res, num_lit(2));
        Ok(())
    }

    #[test]
    fn while_loop() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            block(&[
                helpers::assignment("a".to_string(), num_lit(0)),
                while_expr(
                    binary(BinaryOp::LessThan, iden("a"), num_lit(5)),
                    helpers::assignment(
                        "a".to_string(),
                        binary(BinaryOp::Add, iden("a"), num_lit(1)),
                    ),
                ),
                iden("a"),
            ]),
        )?;
        assert_eq!(res, num_lit(5));
        Ok(())
    }

    #[test]
    fn negate() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(&mut c, unary(UnaryOp::Negate, bool_lit(true)))?;
        assert_eq!(res, bool_lit(false));
        Ok(())
    }

    #[test]
    fn local_scoped_variable() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            block(&[
                block(&[helpers::assignment("a".to_string(), num_lit(42))]),
                iden("a"),
            ]),
        );
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn typed_assignment() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            helpers::assignment_typed("a".to_string(), num_lit(42), "int".to_string()),
        )?;
        assert_eq!(res, num_lit(42));
        Ok(())
    }

    #[test]
    fn typed_assignment_invalid() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            helpers::assignment_typed("a".to_string(), num_lit(42), "string".to_string()),
        );
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn typed_reassignment() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            helpers::assignment_typed("a".to_string(), num_lit(42), "int".to_string()),
        )?;
        assert_eq!(res, num_lit(42));
        Ok(())
    }

    #[test]
    fn string_concat() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            binary(
                BinaryOp::Add,
                string_lit("hello".to_string()),
                string_lit(" world".to_string()),
            ),
        )?;
        assert_eq!(res, string_lit("hello world".to_string()));
        Ok(())
    }

    #[test]
    fn string_concat_num() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            binary(BinaryOp::Add, string_lit("hello".to_string()), num_lit(1)),
        )?;
        assert_eq!(res, string_lit("hello1".to_string()));
        Ok(())
    }

    #[test]
    fn custom_function() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            helpers::function_declaration(
                "add".to_string(),
                vec![("a".to_string(), Some("int".to_string()))],
                iden("a"),
            ),
        )?;
        assert_eq!(res, helpers::no_op());
        let res = interpret(
            &mut c,
            helpers::function_call("add".to_string(), vec![num_lit(1)]),
        )?;
        assert_eq!(res, num_lit(1));
        Ok(())
    }

    #[test]
    fn function_call_wrong_arg_count() -> Result<(), String> {
        let mut c = Context::new();
        interpret(
            &mut c,
            helpers::function_declaration(
                "add".to_string(),
                vec![("a".to_string(), Some("int".to_string()))],
                iden("a"),
            ),
        )
        .unwrap();
        let res = interpret(
            &mut c,
            helpers::function_call("add".to_string(), vec![num_lit(1), num_lit(2)]),
        );
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn function_call_wrong_arg_type() -> Result<(), String> {
        let mut c = Context::new();
        interpret(
            &mut c,
            helpers::function_declaration(
                "add".to_string(),
                vec![("a".to_string(), Some("int".to_string()))],
                iden("a"),
            ),
        )
        .unwrap();
        let res = interpret(
            &mut c,
            helpers::function_call("add".to_string(), vec![string_lit("hello".to_string())]),
        );
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn recursive_function() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            helpers::function_declaration(
                "fact".to_string(),
                vec![("n".to_string(), Some("int".to_string()))],
                helpers::if_expr(
                    binary(BinaryOp::Equal, iden("n"), num_lit(0)),
                    num_lit(1),
                    Some(binary(
                        BinaryOp::Mult,
                        iden("n"),
                        helpers::function_call(
                            "fact".to_string(),
                            vec![binary(BinaryOp::Sub, iden("n"), num_lit(1))],
                        ),
                    )),
                ),
            ),
        )?;
        assert_eq!(res, helpers::no_op());
        let fact5 = interpret(
            &mut c,
            helpers::function_call("fact".to_string(), vec![num_lit(5)]),
        )?;
        assert_eq!(fact5, num_lit(120));
        Ok(())
    }
}
