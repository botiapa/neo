use std::{
    collections::HashMap,
    io::{self, Write, stdout},
};

use tracing::trace;

use crate::{
    expression::{BinaryOp, Expr},
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
    match expr {
        Expr::Binary(op, a, b) => match op {
            BinaryOp::Add => binary_num_op(i32::saturating_add, *a, *b),
            BinaryOp::Sub => binary_num_op(i32::saturating_sub, *a, *b),
            BinaryOp::Mult => binary_num_op(i32::saturating_mul, *a, *b),
            BinaryOp::Div => binary_num_op(i32::saturating_div, *a, *b),
            BinaryOp::GreaterThan => binary_comp_op(i32::gt, *a, *b),
            BinaryOp::GreaterOrEqualThan => binary_comp_op(i32::ge, *a, *b),
            BinaryOp::LessThan => binary_comp_op(i32::lt, *a, *b),
            BinaryOp::LessOrEqualThan => binary_comp_op(i32::le, *a, *b),
            BinaryOp::Equal => binary_comp_op(i32::eq, *a, *b),
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
        Expr::Identifier(var_name) => c
            .get_var(&var_name)
            .ok_or(format!("variable({}) not set", var_name)),
        Expr::Assignment(var_name, value) => interpret_assignment(c, var_name, *value),
        expr => unimplemented!("{:?}", expr),
    }
}

fn interpret_assignment(c: &mut Context, var_name: String, value: Expr) -> Result<Expr, String> {
    let res = c.set_var(&var_name, value)?;
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

fn expect_literal(c: &mut Context, expr: Expr) -> Result<Expr, String> {
    match expr {
        Expr::NumLit(_) | Expr::StringLit(_) => Ok(expr),
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

fn binary_num_op(op_fn: impl Fn(i32, i32) -> i32, a: Expr, b: Expr) -> Result<Expr, String> {
    let a = expect_numlit(&mut Context::new(), a)?;
    let b = expect_numlit(&mut Context::new(), b)?;
    if let (Expr::NumLit(a), Expr::NumLit(b)) = (&a, &b) {
        return Ok(Expr::NumLit(op_fn(*a, *b)).into());
    }
    Err(format!(
        "Invalid operation, expected numbers, got {:?}",
        (a, b)
    ))
}

fn binary_comp_op(op_fn: impl Fn(&i32, &i32) -> bool, a: Expr, b: Expr) -> Result<Expr, String> {
    let a = expect_numlit(&mut Context::new(), a)?;
    let b = expect_numlit(&mut Context::new(), b)?;
    if let (Expr::NumLit(a), Expr::NumLit(b)) = (&a, &b) {
        return Ok(Expr::BoolLit(op_fn(a, b)).into());
    }
    Err(format!(
        "Invalid comparison, expected numbers, got {:?}",
        (a, b)
    ))
}
