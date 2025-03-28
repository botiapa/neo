use crate::expression::Expr;

use super::Type;

#[derive(Debug, Clone, PartialEq)]
pub(super) struct Variable {
    value: Option<Expr>,
    mutable: bool,
    var_type: Option<Type>,
}

impl Variable {
    pub(super) fn new_mutable(value: Option<Expr>) -> Option<Self> {
        Some(Self {
            value,
            var_type: None,
            mutable: true,
        })
    }

    pub(super) fn new_immutable(value: Option<Expr>) -> Option<Self> {
        Some(Self {
            value,
            var_type: None,
            mutable: false,
        })
    }

    pub(super) fn new_mutable_typed(value: Option<Expr>, var_type: Type) -> Result<Self, String> {
        if let Some(value) = &value {
            let new_type = Type::expr_type(&value)
                .ok_or_else(|| format!("Cannot infer type of {:?}", value))?;
            if var_type != new_type {
                return Err(format!("Expected type {:?}, got {:?}", var_type, new_type));
            }
        }
        Ok(Self {
            value,
            var_type: Some(var_type),
            mutable: true,
        })
    }

    pub(super) fn new_immutable_typed(value: Option<Expr>, var_type: Type) -> Result<Self, String> {
        if let Some(value) = &value {
            let new_type = Type::expr_type(&value)
                .ok_or_else(|| format!("Cannot infer type of {:?}", value))?;
            if var_type != new_type {
                return Err(format!("Expected type {:?}, got {:?}", var_type, new_type));
            }
        }
        Ok(Self {
            value,
            var_type: Some(var_type),
            mutable: false,
        })
    }

    pub(super) fn set_value(&mut self, value: Expr) -> Result<Expr, String> {
        if let Some(var_type) = &self.var_type {
            let new_type = Type::expr_type(&value).ok_or("Cannot infer type")?;
            if var_type != &new_type {
                return Err(format!("Expected type {:?}, got {:?}", var_type, new_type));
            }
        }
        self.value = Some(value.clone());
        Ok(value)
    }

    pub(super) fn get_value(&self) -> Option<Expr> {
        self.value.clone()
    }

    pub(super) fn mutable(&self) -> bool {
        self.mutable
    }

    pub(super) fn var_type(&self) -> Option<Type> {
        self.var_type.clone()
    }
}
