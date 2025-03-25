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
    vars: HashMap<String, Variable>,
    stdout: Vec<String>,
}

impl Context {
    pub(crate) fn new() -> Self {
        Self {
            vars: HashMap::new(),
            stdout: Vec::new(),
        }
    }

    pub(crate) fn get_var(&self, name: &str) -> Option<Expr> {
        self.vars.get(name)?.get_value()
    }

    pub(crate) fn set_var(&mut self, name: &String, value: Expr) -> Result<Expr, String> {
        if let Some(var) = self.vars.get_mut(name) {
            if !var.mutable {
                return Err(format!("Cannot mutate immutable variable: {}", name));
            }
            Ok(var.set_value(value))
        } else {
            let var = Variable::new_mutable(Some(value.clone()));
            self.vars.insert(name.to_string(), var);
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
            for expr in expressions {
                last = interpret(c, expr.into())?;
            }
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
        .get_var(&var_name)
        .ok_or(format!("variable({}) not set", var_name))?;
    expect_literal(c, v)
}

fn interpret_assignment(c: &mut Context, var_name: String, value: Expr) -> Result<Expr, String> {
    let lit = expect_literal(c, value)?;
    let res = c.set_var(&var_name, lit)?;
    trace!("Set variable({}) to {:?}", var_name, res);
    Ok(res)
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
    use super::*;

    #[test]
    fn add() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            Expr::Binary(
                BinaryOp::Add,
                Box::new(Expr::NumLit(1)),
                Box::new(Expr::NumLit(2)),
            ),
        )?;
        assert_eq!(res, Expr::NumLit(3));
        Ok(())
    }

    #[test]
    fn assignment() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            Expr::Assignment("a".to_string(), Box::new(Expr::NumLit(1))),
        )?;
        assert_eq!(res, Expr::NumLit(1));
        Ok(())
    }

    #[test]
    fn test_interpret_block() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            Expr::Block(vec![
                Expr::Assignment("a".to_string(), Box::new(Expr::NumLit(1))),
                Expr::Assignment("b".to_string(), Box::new(Expr::NumLit(2))),
                Expr::Binary(
                    BinaryOp::Add,
                    Box::new(Expr::Identifier("a".to_string())),
                    Box::new(Expr::Identifier("b".to_string())),
                ),
            ]),
        )?;
        assert_eq!(res, Expr::NumLit(3));
        Ok(())
    }

    #[test]
    fn yap() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            Expr::Function(
                Token::Ident("yap".to_string()),
                vec![Expr::StringLit("hello".to_string())],
            ),
        )?;
        assert_eq!(res, Expr::NoOp);
        assert_eq!(c.stdout, vec!["hello".to_string()]);
        Ok(())
    }

    #[test]
    fn test_chained_assignment() -> Result<(), String> {
        let mut c = Context::new();
        // a=b=1
        let res = interpret(
            &mut c,
            Expr::Assignment(
                "a".to_string(),
                Box::new(Expr::Assignment("b".to_string(), Box::new(Expr::NumLit(1)))),
            ),
        )?;
        assert_eq!(res, Expr::NumLit(1));
        assert_eq!(c.get_var("a"), Some(Expr::NumLit(1)));
        assert_eq!(c.get_var("b"), Some(Expr::NumLit(1)));
        Ok(())
    }

    #[test]
    fn if_expr() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            Expr::If(
                Box::new(Expr::BoolLit(true)),
                Box::new(Expr::NumLit(1)),
                None,
            ),
        )?;
        assert_eq!(res, Expr::NumLit(1));
        Ok(())
    }

    #[test]
    fn if_else_expr() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            Expr::If(
                Box::new(Expr::BoolLit(false)),
                Box::new(Expr::NumLit(1)),
                Some(Box::new(Expr::NumLit(2))),
            ),
        )?;
        assert_eq!(res, Expr::NumLit(2));
        Ok(())
    }

    #[test]
    fn while_loop() -> Result<(), String> {
        let mut c = Context::new();
        let res = interpret(
            &mut c,
            Expr::Block(vec![
                Expr::Assignment("a".to_string(), Box::new(Expr::NumLit(0))),
                Expr::While(
                    Box::new(Expr::Binary(
                        BinaryOp::LessThan,
                        Box::new(Expr::Identifier("a".to_string())),
                        Box::new(Expr::NumLit(5)),
                    )),
                    Box::new(Expr::Assignment(
                        "a".to_string(),
                        Box::new(Expr::Binary(
                            BinaryOp::Add,
                            Box::new(Expr::Identifier("a".to_string())),
                            Box::new(Expr::NumLit(1)),
                        )),
                    )),
                ),
            ]),
        )?;
        assert_eq!(res, Expr::NumLit(5));
        assert_eq!(c.get_var("a"), Some(Expr::NumLit(5)));
        Ok(())
    }
}
