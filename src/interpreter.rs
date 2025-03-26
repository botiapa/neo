use std::{
    collections::HashMap,
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
}

impl Variable {
    fn new_mutable(value: Option<Expr>) -> Self {
        Self {
            value,
            mutable: true,
        }
    }

    fn set_value(&mut self, value: Expr) -> Expr {
        self.value = Some(value.clone());
        value
    }

    fn get_value(&self) -> Option<Expr> {
        self.value.clone()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Context {
    vars: Vec<HashMap<String, Variable>>,
    stdout: Vec<String>,
}

impl Context {
    pub(crate) fn new() -> Self {
        Self {
            vars: vec![HashMap::new()],
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

    pub(crate) fn set_var(&mut self, name: &String, value: Expr) -> Result<Expr, String> {
        if let Some(var) = self.get_var_mut(name) {
            trace!("Set variable({}) to {:?}", name, value);
            if !var.mutable {
                return Err(format!("Cannot mutate immutable variable: {}", name));
            }
            Ok(var.set_value(value))
        } else {
            trace!("Set new variable({}) to {:?}", name, value);
            let var = Variable::new_mutable(Some(value.clone()));
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
        Expr::Function(Token::Ident(fn_name), args) => interpret_base_function(c, &fn_name, args),
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
        Expr::Assignment(var_name, value) => interpret_assignment(c, var_name, *value),
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

fn interpret_assignment(c: &mut Context, var_name: String, value: Expr) -> Result<Expr, String> {
    let lit = expect_literal(c, value)?;
    c.set_var(&var_name, lit)
}

fn interpret_base_function(c: &mut Context, name: &str, args: Vec<Expr>) -> Result<Expr, String> {
    match name {
        "yap" => yap(c, args.get(0).ok_or("Expected an argument")?),
        _ => unimplemented!(),
    }
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

fn yap(c: &mut Context, output: &Expr) -> Result<Expr, String> {
    let arg = expect_literal(c, output.clone())?;
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

fn binary_num_op(
    c: &mut Context,
    op_fn: impl Fn(i32, i32) -> i32,
    a: Expr,
    b: Expr,
) -> Result<Expr, String> {
    let a = expect_numlit(c, a)?;
    let b = expect_numlit(c, b)?;
    if let (Expr::NumLit(a), Expr::NumLit(b)) = (&a, &b) {
        return Ok(Expr::NumLit(op_fn(*a, *b)).into());
    }
    Err(format!(
        "Invalid operation, expected numbers, got {:?}",
        (a, b)
    ))
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
}
