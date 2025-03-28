use std::collections::HashMap;

use crate::expression::Expr;

use super::{Type, Variable};

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ScopeManager {
    global_scope: HashMap<String, Variable>,
    scopes: Vec<HashMap<String, Variable>>,
}

impl ScopeManager {
    pub fn new() -> Self {
        Self {
            global_scope: HashMap::new(),
            scopes: vec![],
        }
    }

    pub(crate) fn get_var_value(&self, name: &str) -> Option<Expr> {
        self.get_var(name).map(|v| v.get_value())?
    }

    pub(crate) fn get_var(&self, name: &str) -> Option<&Variable> {
        // search in scopes from inner to outer then global scope
        self.scopes
            .iter()
            .rev()
            .find_map(|vars| vars.get(name))
            .or_else(|| self.global_scope.get(name))
    }

    pub(crate) fn get_var_mut(&mut self, name: &str) -> Option<&mut Variable> {
        self.scopes
            .iter_mut()
            .rev()
            .find_map(|vars| vars.get_mut(name))
            .or_else(|| self.global_scope.get_mut(name))
    }

    pub(crate) fn new_var(
        &mut self,
        name: &str,
        value: Expr,
        var_type: Option<Type>,
    ) -> Result<(), String> {
        let var = match var_type {
            Some(var_type) => Variable::new_mutable_typed(Some(value), var_type)?,
            None => Variable::new_mutable(Some(value))
                .ok_or(format!("Failed to create variable: {}", name))?,
        };
        self.scopes
            .last_mut()
            .unwrap_or(&mut self.global_scope)
            .insert(name.to_string(), var);
        Ok(())
    }

    pub(crate) fn in_global_scope(&self) -> bool {
        self.scopes.len() == 0
    }

    pub(crate) fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub(crate) fn leave_scope(&mut self) {
        self.scopes.pop();
    }
}
