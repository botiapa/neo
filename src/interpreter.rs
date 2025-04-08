use core::fmt;
use std::{
    collections::HashMap,
    fmt::Display,
    io::{self, Write, stdout},
};

use enum_type::Enum;
use functions::{EnumConstructor, Function};
use scope_manager::ScopeManager;
use tracing::trace;
use variable::Variable;

mod builtin_functions;
mod enum_type;
mod functions;
mod helpers;
mod operators;
mod scope_manager;
mod variable;

use crate::{
    expression::{BinaryOp, EnumDeclaration, EnumVariant, Expr, Id, Path, UnaryOp, VarType},
    tokenizer::Token,
};

#[derive(Debug, Clone, PartialEq)]
enum Type {
    Int,
    String,
    Bool,
    Enum(Enum),
    EnumVariant(EnumVariant),
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
            Expr::EnumDeclaration(EnumDeclaration { name, variants }) => Some(Type::Enum(Enum {
                name: name.clone(),
                variants: variants.clone(),
            })),
            Expr::EnumVariant(EnumVariant {
                enum_name,
                variant_name,
                values,
            }) => Some(Type::EnumVariant(EnumVariant {
                enum_name: enum_name.clone(),
                variant_name: variant_name.clone(),
                values: values.clone(),
            })),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Context {
    scopes: ScopeManager,
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
            scopes: ScopeManager::new(),
            functions: HashMap::new(),
            types,
            stdout: Vec::new(),
        }
    }

    pub(crate) fn set_var(
        &mut self,
        name: &String,
        value: Expr,
        var_type: Option<VarType>,
    ) -> Result<Expr, String> {
        let new_var_type = match var_type {
            Some(var_type) => Some(
                self.types
                    .get(&type_path_to_string(&var_type))
                    .ok_or(format!("Invalid type: {}", type_path_to_string(&var_type)))?
                    .clone(),
            ),
            None => None,
        };

        if let Some(var) = self.scopes.get_var_mut(name) {
            trace!("Set variable({}) to {:?}", name, value);
            if !var.mutable() {
                return Err(format!("Cannot mutate immutable variable: {}", name));
            }
            if let Some(var_type) = new_var_type {
                if Some(var_type) != var.var_type() {
                    return Err(format!(
                        "Cannot reassign variable({}) to {:?} (invalid type?)",
                        name, value
                    ));
                }
            }
            var.set_value(value)
        } else {
            trace!("Set new variable({}) to {:?}", name, value);
            self.scopes.new_var(name, value.clone(), new_var_type)?;
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

    pub(crate) fn interpret(&mut self, expr: Expr) -> Result<Expr, String> {
        Ok(match expr {
            Expr::Block(exprs) => {
                let mut last = Expr::NoOp;
                for expr in exprs {
                    last = self.interpret_expr(expr)?;
                }
                last
            }
            _ => self.interpret_expr(expr)?,
        })
    }

    fn interpret_expr(&mut self, expr: Expr) -> Result<Expr, String> {
        trace!("Interpreting: {:?}, context: {:?}", expr, self);
        match expr {
            Expr::Unary(op, a) => match op {
                UnaryOp::Plus => self.interpret_expr(*a),
                UnaryOp::Minus => self.binary_num_op(i32::saturating_sub, Expr::NumLit(0), *a),
                UnaryOp::Negate => self.negate(*a),
            },
            Expr::Binary(op, a, b) => match op {
                BinaryOp::Add => self.binary_num_op(i32::saturating_add, *a, *b),
                BinaryOp::Sub => self.binary_num_op(i32::saturating_sub, *a, *b),
                BinaryOp::Mult => self.binary_num_op(i32::saturating_mul, *a, *b),
                BinaryOp::Div => self.binary_num_op(i32::saturating_div, *a, *b),
                BinaryOp::GreaterThan => self.binary_comp_op(i32::gt, *a, *b),
                BinaryOp::GreaterOrEqualThan => self.binary_comp_op(i32::ge, *a, *b),
                BinaryOp::LessThan => self.binary_comp_op(i32::lt, *a, *b),
                BinaryOp::LessOrEqualThan => self.binary_comp_op(i32::le, *a, *b),
                BinaryOp::Equal => self.binary_comp_op(i32::eq, *a, *b),
            },
            Expr::FunctionCall(Token::Ident(fn_name), args) => {
                self.interpret_function_call(&fn_name, args)
            }
            Expr::FunctionDeclaration(name, args, body) => {
                self.interpret_function_declaration(&name, args, *body)
            }
            Expr::EnumDeclaration(enum_decl) => self.interpret_enum_declaration(&enum_decl),
            Expr::Block(expressions) => {
                let mut last = Expr::NoOp;
                self.scopes.enter_scope();
                for expr in expressions {
                    last = self.interpret_expr(expr.into())?;
                }
                self.scopes.leave_scope();
                Ok(last)
            }
            Expr::NumLit(_) | Expr::StringLit(_) | Expr::BoolLit(_) | Expr::EnumVariant(_) => {
                Ok(expr)
            }
            Expr::Identifier(var_name, path) => self.interpret_identifier(var_name, path),
            Expr::Assignment(var_name, value, var_type) => {
                self.interpret_assignment(var_name, *value, var_type)
            }
            Expr::If(cond, then, else_) => self.interpret_if(*cond, *then, else_.map(|e| *e)),
            Expr::While(cond, body) => self.interpet_while(*cond, *body),
            Expr::Is(iden, enum_variant) => self.interpret_is(iden, *enum_variant),
            expr => unimplemented!("{:?}", expr),
        }
    }

    fn interpet_while(&mut self, cond: Expr, body: Expr) -> Result<Expr, String> {
        let mut res = Expr::NoOp;
        trace!("Interpreting while: {:?}, body: {:?}", cond, body);
        loop {
            let cond = self.expect_boollit(cond.clone())?;
            if !cond {
                break;
            }
            res = self.interpret_expr(body.clone())?;
        }
        trace!("Exiting while loop, result: {:?}", res);
        Ok(res)
    }

    fn interpret_if(
        &mut self,
        cond: Expr,
        then: Expr,
        else_: Option<Expr>,
    ) -> Result<Expr, String> {
        let cond = self.expect_boollit(cond)?;
        trace!(
            "Interpreting if: {:?}, then: {:?}, else: {:?}",
            cond, then, else_
        );
        if cond {
            self.interpret_expr(then)
        } else {
            if let Some(else_) = else_ {
                self.interpret_expr(else_)
            } else {
                Ok(Expr::NoOp)
            }
        }
    }

    fn interpret_identifier(&mut self, var_name: String, path: Path) -> Result<Expr, String> {
        if path.len() > 0 {
            return Err(format!("Expected a variable, got {:?}", path));
        }

        let v = self
            .scopes
            .get_var_value(&var_name)
            .ok_or(format!("variable({}) not set", var_name))?;
        self.expect_literal(v)
    }

    fn interpret_assignment(
        &mut self,
        var_name: Id,
        value: Expr,
        var_type: Option<VarType>,
    ) -> Result<Expr, String> {
        let lit = self.expect_literal(value)?;
        self.set_var(&var_name, lit, var_type)
    }

    fn interpret_enum_declaration(&mut self, enum_decl: &EnumDeclaration) -> Result<Expr, String> {
        if !self.scopes.in_global_scope() {
            return Err(format!(
                "Enum({}) cannot be declared in a non-global scope",
                enum_decl.name
            ));
        }

        trace!(
            "Declaring enum({}) with variants: {:?}",
            enum_decl.name, enum_decl.variants
        );

        // Each variant must be unique
        let mut variant_names = HashMap::new();
        for (variant_name, args) in enum_decl.variants.iter() {
            if variant_names.contains_key(variant_name) {
                return Err(format!("Variant({}) already declared", variant_name));
            }
            variant_names.insert(variant_name.clone(), args.clone());
        }

        // Each variant is a constructor of this type
        for (variant_name, args) in enum_decl.variants.iter() {
            if args.is_some() {
                self.functions.insert(
                    variant_name.to_string(),
                    Function::EnumConstructor(EnumConstructor {
                        enum_name: enum_decl.name.to_string(),
                        variant_name: variant_name.to_string(),
                        args_types: args.clone().unwrap_or_default(),
                    }),
                );
            } else {
                let enum_var = EnumVariant {
                    enum_name: enum_decl.name.to_string(),
                    variant_name: variant_name.to_string(),
                    values: vec![],
                };
                self.scopes.new_var(
                    variant_name,
                    Expr::EnumVariant(enum_var.clone()),
                    Some(Type::EnumVariant(enum_var)),
                )?;
            }
        }

        if self.types.contains_key(&enum_decl.name) {
            return Err(format!("Type({}) already declared", enum_decl.name));
        }

        let enum_type = Type::Enum(Enum {
            name: enum_decl.name.to_string(),
            variants: enum_decl.variants.clone(),
        });
        self.types.insert(enum_decl.name.to_string(), enum_type);
        Ok(Expr::NoOp)
    }

    fn interpret_is(&mut self, iden: Id, enum_variant: Expr) -> Result<Expr, String> {
        let var_value = self
            .scopes
            .get_var_value(&iden)
            .ok_or(format!("Variable({}) not set", iden))?;

        let enum_variant = self.expect_literal(enum_variant)?;
        Ok(Expr::NoOp)
    }

    const DEFAULT_TYPES: [(&'static str, Type); 4] = [
        ("int", Type::Int),
        ("string", Type::String),
        ("bool", Type::Bool),
        ("drip", Type::Int),
    ];
}

// FIXME: This is a hack before namespaces are correctly implemented
fn type_path_to_string(var_type: &VarType) -> String {
    let (name, path) = var_type;
    if path.len() > 0 {
        format!("{}::{}", name, path.join("::"))
    } else {
        name.clone()
    }
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
        let res = c.interpret_expr(binary(BinaryOp::Add, num_lit(1), num_lit(2)))?;
        assert_eq!(res, num_lit(3));
        Ok(())
    }

    #[test]
    fn assignment() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(helpers::assignment("a".to_string(), num_lit(1)))?;
        assert_eq!(res, num_lit(1));
        Ok(())
    }

    #[test]
    fn test_interpret_block() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(block(&[
            helpers::assignment("a".to_string(), num_lit(1)),
            helpers::assignment("b".to_string(), num_lit(2)),
            binary(BinaryOp::Add, iden("a"), iden("b")),
        ]))?;
        assert_eq!(res, num_lit(3));
        Ok(())
    }

    #[test]
    fn yap() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(function(
            Token::Ident("yap".to_string()),
            vec![string_lit("hello".to_string())],
        ))?;
        assert_eq!(res, helpers::no_op());
        assert_eq!(c.stdout, vec!["hello".to_string()]);
        Ok(())
    }

    #[test]
    fn test_chained_assignment() -> Result<(), String> {
        let mut c = Context::new();
        // a=b=1
        let res = c.interpret_expr(helpers::assignment(
            "a".to_string(),
            helpers::assignment("b".to_string(), num_lit(1)),
        ))?;
        assert_eq!(res, num_lit(1));
        assert_eq!(c.scopes.get_var_value("a"), Some(num_lit(1)));
        assert_eq!(c.scopes.get_var_value("b"), Some(num_lit(1)));
        Ok(())
    }

    #[test]
    fn if_expr() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(helpers::if_expr(bool_lit(true), num_lit(1), None))?;
        assert_eq!(res, num_lit(1));
        Ok(())
    }

    #[test]
    fn if_else_expr() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(helpers::if_expr(
            bool_lit(false),
            num_lit(1),
            Some(num_lit(2)),
        ))?;
        assert_eq!(res, num_lit(2));
        Ok(())
    }

    #[test]
    fn while_loop() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(block(&[
            helpers::assignment("a".to_string(), num_lit(0)),
            while_expr(
                binary(BinaryOp::LessThan, iden("a"), num_lit(5)),
                helpers::assignment(
                    "a".to_string(),
                    binary(BinaryOp::Add, iden("a"), num_lit(1)),
                ),
            ),
            iden("a"),
        ]))?;
        assert_eq!(res, num_lit(5));
        Ok(())
    }

    #[test]
    fn negate() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(unary(UnaryOp::Negate, bool_lit(true)))?;
        assert_eq!(res, bool_lit(false));
        Ok(())
    }

    #[test]
    fn local_scoped_variable() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(block(&[
            block(&[helpers::assignment("a".to_string(), num_lit(42))]),
            iden("a"),
        ]));
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn typed_assignment() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(helpers::assignment_typed(
            "a".to_string(),
            num_lit(42),
            ("int".to_string(), vec![]),
        ))?;
        assert_eq!(res, num_lit(42));
        Ok(())
    }

    #[test]
    fn typed_assignment_invalid() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(helpers::assignment_typed(
            "a".to_string(),
            num_lit(42),
            ("string".to_string(), vec![]),
        ));
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn typed_reassignment() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(helpers::assignment_typed(
            "a".to_string(),
            num_lit(42),
            ("int".to_string(), vec![]),
        ))?;
        assert_eq!(res, num_lit(42));
        Ok(())
    }

    #[test]
    fn string_concat() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(binary(
            BinaryOp::Add,
            string_lit("hello".to_string()),
            string_lit(" world".to_string()),
        ))?;
        assert_eq!(res, string_lit("hello world".to_string()));
        Ok(())
    }

    #[test]
    fn string_concat_num() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(binary(
            BinaryOp::Add,
            string_lit("hello".to_string()),
            num_lit(1),
        ))?;
        assert_eq!(res, string_lit("hello1".to_string()));
        Ok(())
    }

    #[test]
    fn custom_function() -> Result<(), String> {
        // fn add(int a) {a}
        let mut c = Context::new();
        let res = c.interpret_expr(helpers::function_declaration(
            "add".to_string(),
            vec![("a".to_string(), Some(("int".to_string(), vec![])))],
            iden("a"),
        ))?;
        assert_eq!(res, helpers::no_op());
        let res = c.interpret_expr(helpers::function_call("add".to_string(), vec![num_lit(1)]))?;
        assert_eq!(res, num_lit(1));
        Ok(())
    }

    #[test]
    fn function_call_wrong_arg_count() -> Result<(), String> {
        let mut c = Context::new();
        c.interpret_expr(helpers::function_declaration(
            "add".to_string(),
            vec![("a".to_string(), Some(("int".to_string(), vec![])))],
            iden("a"),
        ))
        .unwrap();
        let res = c.interpret_expr(helpers::function_call(
            "add".to_string(),
            vec![num_lit(1), num_lit(2)],
        ));
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn function_call_wrong_arg_type() -> Result<(), String> {
        let mut c = Context::new();
        c.interpret_expr(helpers::function_declaration(
            "add".to_string(),
            vec![("a".to_string(), Some(("int".to_string(), vec![])))],
            iden("a"),
        ))
        .unwrap();
        let res = c.interpret_expr(helpers::function_call(
            "add".to_string(),
            vec![string_lit("hello".to_string())],
        ));
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn recursive_function() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(helpers::function_declaration(
            "fact".to_string(),
            vec![("n".to_string(), Some(("int".to_string(), vec![])))],
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
        ))?;
        assert_eq!(res, helpers::no_op());
        let fact5 =
            c.interpret_expr(helpers::function_call("fact".to_string(), vec![num_lit(5)]))?;
        assert_eq!(fact5, num_lit(120));
        Ok(())
    }

    #[test]
    fn enum_declaration() -> Result<(), String> {
        let mut c = Context::new();
        let res = c.interpret_expr(helpers::enum_dec(
            "Option".to_string(),
            vec![
                ("Some".to_string(), Some(vec!["int".to_string()])),
                ("None".to_string(), None),
            ],
        ))?;
        assert_eq!(res, helpers::no_op());
        assert_eq!(
            c.types.get("Option"),
            Some(&Type::Enum(Enum {
                name: "Option".to_string(),
                variants: vec![
                    ("Some".to_string(), Some(vec!["int".to_string()])),
                    ("None".to_string(), None),
                ],
            }))
        );
        Ok(())
    }

    #[test]
    fn enum_declaration_already_declared() -> Result<(), String> {
        let mut c = Context::new();
        c.interpret_expr(helpers::enum_dec("Option".to_string(), vec![]))?;
        assert!(
            c.interpret_expr(helpers::enum_dec("Option".to_string(), vec![]))
                .is_err()
        );
        Ok(())
    }

    #[test]
    fn fn_declaration_already_declared() -> Result<(), String> {
        let mut c = Context::new();
        c.interpret_expr(helpers::function_declaration(
            "add".to_string(),
            vec![],
            iden("a"),
        ))?;
        assert!(
            c.interpret_expr(helpers::function_declaration(
                "add".to_string(),
                vec![],
                iden("a")
            ))
            .is_err()
        );
        Ok(())
    }

    #[test]
    fn enum_value_without_param() -> Result<(), String> {
        let mut c = Context::new();
        c.interpret_expr(helpers::enum_dec(
            "Option".to_string(),
            vec![
                ("Some".to_string(), Some(vec!["int".to_string()])),
                ("None".to_string(), None),
            ],
        ))?;
        let res = c.interpret_expr(helpers::iden(&"None"))?;
        assert_eq!(
            res,
            Expr::EnumVariant(EnumVariant {
                enum_name: "Option".to_string(),
                variant_name: "None".to_string(),
                values: vec![],
            })
        );
        Ok(())
    }

    #[test]
    fn enum_value_with_param() -> Result<(), String> {
        let mut c = Context::new();
        c.interpret_expr(helpers::enum_dec(
            "Option".to_string(),
            vec![
                ("Some".to_string(), Some(vec!["int".to_string()])),
                ("None".to_string(), None),
            ],
        ))?;
        let res = c.interpret_expr(helpers::function_call(
            "Some".to_string(),
            vec![num_lit(42)],
        ))?;
        assert_eq!(
            res,
            Expr::EnumVariant(EnumVariant {
                enum_name: "Option".to_string(),
                variant_name: "Some".to_string(),
                values: vec![num_lit(42)],
            })
        );
        Ok(())
    }

    #[test]
    fn enum_variant_type() -> Result<(), String> {
        // enum A {B(int)}; B(true)
        // should be an error
        let mut c = Context::new();
        let res = c.interpret_expr(helpers::enum_dec(
            "A".to_string(),
            vec![("B".to_string(), Some(vec!["int".to_string()]))],
        ))?;
        assert_eq!(res, helpers::no_op());
        let res = c.interpret_expr(helpers::function_call(
            "B".to_string(),
            vec![bool_lit(true)],
        ));
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn enum_in_non_global_scope() -> Result<(), String> {
        // {enum A {}} -> should be an error
        let mut c = Context::new();
        let res = c.interpret_expr(block(&[helpers::enum_dec("A".to_string(), vec![])]));
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn fn_in_non_global_scope() -> Result<(), String> {
        // {fn a() {}} -> should be an error
        let mut c = Context::new();
        let res = c.interpret_expr(block(&[helpers::function_declaration(
            "a".to_string(),
            vec![],
            helpers::no_op(),
        )]));
        assert!(res.is_err());
        Ok(())
    }
}
