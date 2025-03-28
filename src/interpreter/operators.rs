use crate::expression::Expr;

use super::Context;

impl Context {
    pub(super) fn negate(&mut self, expr: Expr) -> Result<Expr, String> {
        let lit = self.expect_boollit(expr)?;
        Ok(Expr::BoolLit(!lit))
    }

    pub(super) fn binary_num_op(
        &mut self,
        op_fn: impl Fn(i32, i32) -> i32,
        a: Expr,
        b: Expr,
    ) -> Result<Expr, String> {
        let a = self.expect_literal(a)?;
        let b = self.expect_literal(b)?;
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

    pub(super) fn binary_comp_op(
        &mut self,
        op_fn: impl Fn(&i32, &i32) -> bool,
        a: Expr,
        b: Expr,
    ) -> Result<Expr, String> {
        let a = self.expect_numlit(a)?;
        let b = self.expect_numlit(b)?;
        if let (Expr::NumLit(a), Expr::NumLit(b)) = (&a, &b) {
            return Ok(Expr::BoolLit(op_fn(a, b)).into());
        }
        Err(format!(
            "Invalid comparison, expected numbers, got {:?}",
            (a, b)
        ))
    }
}
