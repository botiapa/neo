use crate::tokenizer::Token;

use super::{Args, BinaryOp, EnumDeclaration, EnumVariant, Expr, Parser, UnaryOp, VarType};

pub(crate) fn num_lit(n: i32) -> Expr {
    Expr::NumLit(n)
}

pub(crate) fn string_lit(s: String) -> Expr {
    Expr::StringLit(s)
}

pub(crate) fn bool_lit(b: bool) -> Expr {
    Expr::BoolLit(b)
}

pub(crate) fn iden(id: &str) -> Expr {
    Expr::Identifier(id.to_string(), vec![])
}

pub(crate) fn iden_with_path(id: &str, path: Vec<String>) -> Expr {
    Expr::Identifier(id.to_string(), path)
}

pub(crate) fn unary(op: UnaryOp, expr: Expr) -> Expr {
    Expr::Unary(op, Box::new(expr))
}

pub(crate) fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::Binary(op, Box::new(left), Box::new(right))
}

pub(crate) fn function(name: String, args: Vec<Expr>) -> Expr {
    Expr::FunctionCall(name, args)
}

pub(crate) fn function_call(name: String, args: Vec<Expr>) -> Expr {
    Expr::FunctionCall(name, args)
}

pub(crate) fn block(exprs: &[Expr]) -> Expr {
    Expr::Block(exprs.to_vec())
}

pub(crate) fn assignment(id: String, expr: Expr) -> Expr {
    Expr::Assignment(id, Box::new(expr), None)
}

pub(crate) fn assignment_typed(id: String, expr: Expr, var_type: VarType) -> Expr {
    Expr::Assignment(id, Box::new(expr), Some(var_type))
}

pub(crate) fn if_expr(cond: Expr, then: Expr, else_block: Option<Expr>) -> Expr {
    Expr::If(Box::new(cond), Box::new(then), else_block.map(Box::new))
}

pub(crate) fn while_expr(cond: Expr, block: Expr) -> Expr {
    Expr::While(Box::new(cond), Box::new(block))
}

pub(crate) fn enum_dec(name: String, variants: Vec<(String, Option<Vec<String>>)>) -> Expr {
    Expr::EnumDeclaration(EnumDeclaration { name, variants })
}

pub(crate) fn no_op() -> Expr {
    Expr::NoOp
}

pub(crate) fn function_declaration(name: String, args: Args, body: Expr) -> Expr {
    Expr::FunctionDeclaration(name, args, Box::new(body))
}

pub(crate) fn enum_variant(enum_name: &str, variant_name: &str, values: Vec<Expr>) -> Expr {
    Expr::EnumVariant(EnumVariant {
        enum_name: enum_name.to_string(),
        variant_name: variant_name.to_string(),
        values,
    })
}

pub(crate) fn is_expr(iden: &str, enum_variant: Expr) -> Expr {
    Expr::Is(iden.to_string(), Box::new(enum_variant))
}
