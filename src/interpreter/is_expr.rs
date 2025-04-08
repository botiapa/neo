use std::collections::HashMap;

use tracing::trace;

use crate::expression::{EnumVariant, Expr, Id, helpers::bool_lit};

use super::{
    Context, Type,
    functions::{EnumConstructor, Function},
    scope_manager::ScopeManager,
};

impl Context {
    /// Interprets an `is` expression.
    ///
    /// Example:
    /// ```
    /// enum A {B, C, D(int)}
    /// a = B
    /// a is B == true
    /// a is C == false
    /// b = D(1)
    /// b is D(n) == true
    /// ```
    pub(super) fn interpret_is_expr(&mut self, iden: Id, right: Expr) -> Result<Expr, String> {
        let left_enum_variant = match self.scopes.get_var_value(&iden) {
            Some(Expr::EnumVariant(enum_variant)) => enum_variant,
            Some(_) => {
                return Err(format!("Variable({}) is not an enum variant", iden));
            }
            None => {
                return Err(format!(
                    "Variable({}) not set when interpreting `is` expression",
                    iden
                ));
            }
        };

        // example: a is B or a is B(n)
        match right {
            Expr::Identifier(iden, _) => self.simple_enum_variant(&left_enum_variant, &iden),
            Expr::FunctionCall(iden, args) => {
                let enum_constructor = match self.functions.get(&iden) {
                    Some(Function::EnumConstructor(enum_constructor)) => enum_constructor,
                    _ => return Err(format!("Function({}) is not an enum constructor", iden)),
                }
                .clone();
                self.complex_enum_variant(&left_enum_variant, enum_constructor, &args)
            }
            _ => return Err(format!("Expected an identifier, got {:?}", right)),
        }
    }

    fn simple_enum_variant(
        &self,
        left_enum_variant: &EnumVariant,
        iden: &Id,
    ) -> Result<Expr, String> {
        let (_, right_enum_variant) = match self.scopes.get_var(&iden) {
            Some(var) => match var.var_type() {
                Some(Type::EnumVariant(enum_variant)) => (var, enum_variant),
                _ => return Err(format!("Variable({}) is not an enum variant", iden)),
            },
            None => {
                return Err(format!(
                    "Variable({}) not set when interpreting `is` expression",
                    iden
                ));
            }
        };

        Ok(bool_lit(*left_enum_variant == right_enum_variant))
    }

    fn complex_enum_variant(
        &mut self,
        left_enum_variant: &EnumVariant,
        enum_constructor: EnumConstructor,
        args: &Vec<Expr>,
    ) -> Result<Expr, String> {
        if left_enum_variant.enum_name != enum_constructor.enum_name
            || left_enum_variant.variant_name != enum_constructor.variant_name
        {
            return Ok(bool_lit(false));
        }

        // We know the enum name and variant name are the same, so we can start comparing and binding the args
        // We know the values of the left must be literals, but the right can either be an ident meaning we need to bind
        // or a literal meaning we can just compare
        for (left_val, (right_val, arg_type)) in left_enum_variant
            .values
            .iter()
            .zip(args.iter().zip(enum_constructor.args_types.iter()))
        {
            match right_val {
                // binding
                Expr::Identifier(iden, _) => {
                    Self::try_bind(&self.types, &mut self.scopes, iden, left_val, &arg_type)?;
                }
                // enum constructor or named function call
                Expr::FunctionCall(iden, args) => {
                    let right_inside_enum_ctr = self.try_extract_enum(iden)?;
                    if let Expr::EnumVariant(left_inside_enum_variant) = left_val {
                        return self.complex_enum_variant(
                            left_inside_enum_variant,
                            right_inside_enum_ctr,
                            args,
                        );
                    } else {
                        return Err(format!(
                            "Expected an enum variant on the left, got {:?}",
                            left_val
                        ));
                    }
                }
                _ => {
                    if left_val != right_val {
                        return Ok(bool_lit(false));
                    }
                }
            }
        }

        Ok(bool_lit(true))
    }

    fn try_bind(
        types: &HashMap<String, Type>,
        scopes: &mut ScopeManager,
        iden: &Id,
        left_val: &Expr,
        arg_type: &str,
    ) -> Result<(), String> {
        let arg_type = types
            .get(arg_type)
            .expect("arg type should exist given enum constructors are created by the interpreter")
            .clone();
        scopes.new_var(&iden, left_val.clone(), Some(arg_type))?;
        trace!("Bound {} to {:?}", iden, left_val);
        Ok(())
    }

    fn try_extract_enum(&self, iden: &Id) -> Result<EnumConstructor, String> {
        let func = self
            .functions
            .get(iden)
            .ok_or(format!("Function({}) not found", iden))?
            .clone();
        match func {
            Function::EnumConstructor(func) => Ok(func),
            _ => Err(format!(
                "Function({}) is not an enum constructor on the right side of an is expression",
                iden
            )),
        }
    }
}
