use tracing::trace;

use crate::{expression::Expr, interpreter::type_path_to_string};

use super::{Context, Type};

impl Context {
    /// Prints the argument to the stdout
    pub(super) fn yap(&mut self, p1: &Expr) -> Result<Expr, String> {
        let arg = self.expect_literal(p1.clone())?;
        let s = match arg {
            Expr::NumLit(a) => a.to_string(),
            Expr::StringLit(s) => s.replace("\\n", "\n"),
            _ => {
                return Err(format!(
                    "Invalid argument, expected number or string, got {:?}",
                    arg
                ));
            }
        };
        self.stdout.push(s);
        Ok(Expr::NoOp)
    }

    /// Returns the argument's type as string
    pub(super) fn vibe(&mut self, p1: &Expr) -> Result<Expr, String> {
        let arg = self.expect_literal(p1.clone())?;
        match p1 {
            Expr::Identifier(name, path) => {
                trace!("Vibing identifier({}) with path: {:?}", name, path);
                let var = self
                    .scopes
                    .get_var(&type_path_to_string(&(name.to_string(), path.clone())))
                    .ok_or(format!("Variable({}) not found", name))?;
                Ok(Expr::StringLit(
                    var.var_type()
                        .as_ref()
                        .map(|t| t.to_string())
                        .unwrap_or("vibeless".to_string()),
                ))
            }
            Expr::NumLit(_) | Expr::StringLit(_) | Expr::BoolLit(_) => {
                Ok(Expr::StringLit(Type::expr_type(&arg).unwrap().to_string()))
            }
            expr => unimplemented!("vibe({:?})", expr),
        }
    }
}
