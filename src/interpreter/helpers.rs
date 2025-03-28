use crate::expression::Expr;

use super::Context;

impl Context {
    pub(super) fn expect_numlit(&mut self, expr: Expr) -> Result<Expr, String> {
        match expr {
            Expr::NumLit(_) => Ok(expr),
            _ => self.interpret(expr),
        }
    }

    pub(super) fn expect_boollit(&mut self, expr: Expr) -> Result<bool, String> {
        match expr {
            Expr::BoolLit(b) => Ok(b),
            _ => match self.interpret(expr) {
                Ok(Expr::BoolLit(b)) => Ok(b),
                Ok(expr) => Err(format!("Expected a boolean, got {:?}", expr)),
                Err(err) => Err(err),
            },
        }
    }

    pub(super) fn expect_literal(&mut self, expr: Expr) -> Result<Expr, String> {
        match expr {
            Expr::NumLit(_) | Expr::StringLit(_) | Expr::BoolLit(_) => Ok(expr),
            _ => self.interpret(expr),
        }
    }
}
