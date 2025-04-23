use core::fmt;
use std::fmt::Display;

use crate::expression::{EnumVariant, Expr};

use super::{Context, Type, functions::EnumConstructor};

type VariantName = String;
type VariantParameters = Option<Vec<String>>;
type EnumVariantType = (VariantName, VariantParameters);
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Enum {
    pub(super) name: String,
    pub(super) variants: Vec<EnumVariantType>,
}

impl Display for Enum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Enum({})", self.name)
    }
}

impl Context {
    pub(super) fn interpret_enum_constructor(
        &mut self,
        func: &EnumConstructor,
        args: Vec<Expr>,
    ) -> Result<Expr, String> {
        if func.args_types.len() != args.len() {
            return Err(format!(
                "Expected {} arguments, got {}",
                func.args_types.len(),
                args.len()
            ));
        }
        let values = args
            .into_iter()
            .map(|arg| self.expect_literal(arg))
            .collect::<Result<Vec<_>, String>>()?;

        // Check if arg types match the variant's type
        for (i, (arg_type, arg)) in func.args_types.iter().zip(values.iter()).enumerate() {
            let expected_arg_type = self
                .types
                .get(arg_type)
                .ok_or(format!("Type({}) not found", arg_type))?;
            let arg = Type::expr_type(arg).ok_or(format!("Cannot infer type of {:?}", arg))?;

            if !enum_arg_types_match(expected_arg_type, &arg) {
                return Err(format!(
                    "Expected type({}) for argument({}), got type({})",
                    expected_arg_type, i, arg
                ));
            }
        }

        Ok(Expr::EnumVariant(EnumVariant {
            enum_name: func.enum_name.clone(),
            variant_name: func.variant_name.clone(),
            values,
        }))
    }
}

fn enum_arg_types_match(expected_arg_type: &Type, arg: &Type) -> bool {
    match (expected_arg_type, arg) {
        (Type::Enum(expected_enum), Type::EnumVariant(enumvariant))
            if enumvariant.enum_name == expected_enum.name =>
        {
            true
        }
        (a, b) if a == b => true,
        _ => false,
    }
}
