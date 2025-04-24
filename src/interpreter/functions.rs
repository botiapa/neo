use tracing::trace;

use crate::expression::{Args, Expr, FunctionDeclaration};

use super::{Context, Type, type_path_to_string};

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct NamedFunction {
    pub(crate) args: Vec<(String, Option<Type>)>,
    pub(crate) body: Expr,
    pub(crate) generic_args: Option<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct EnumConstructor {
    pub(crate) enum_name: String,
    pub(crate) variant_name: String,
    pub(crate) args_types: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Function {
    NamedFunction(NamedFunction),
    EnumConstructor(EnumConstructor),
}

impl Context {
    pub(super) fn interpret_function_call(
        &mut self,
        name: &str,
        args: Vec<Expr>,
    ) -> Result<Expr, String> {
        match name {
            "yap" => self.yap(args.get(0).ok_or("Expected an argument")?),
            "vibe" => self.vibe(args.get(0).ok_or("Expected an argument")?),
            fn_name => {
                let func = self
                    .functions
                    .get(fn_name)
                    .ok_or(format!("Function({}) not found", fn_name))?
                    .clone();
                trace!("Interpreting function({}) with args: {:?}", fn_name, args);
                match func {
                    Function::NamedFunction(func) => self.interpret_named_function(&func, args),
                    Function::EnumConstructor(func) => self.interpret_enum_constructor(&func, args),
                }
            }
        }
    }

    pub(super) fn interpret_function_declaration(
        &mut self,
        FunctionDeclaration {
            name,
            args,
            generic_args,
            body,
        }: FunctionDeclaration,
    ) -> Result<Expr, String> {
        if self.functions.contains_key(&name) {
            return Err(format!("Function({}) already declared", name));
        }

        if !self.scopes.in_global_scope() {
            return Err(format!(
                "Function({}) cannot be declared in a non-global scope",
                name
            ));
        }

        let args = args
            .into_iter()
            .map(|(name, var_type)| {
                (
                    name,
                    var_type.map(|t| {
                        self.types
                            .get(&type_path_to_string(&t))
                            .expect(format!("Invalid type: {}", type_path_to_string(&t)).as_str())
                            .clone()
                    }),
                )
            })
            .collect();
        self.functions.insert(
            name.to_string(),
            Function::NamedFunction(NamedFunction {
                args,
                body: *body,
                generic_args,
            }),
        );
        Ok(Expr::NoOp)
    }

    fn interpret_named_function(
        &mut self,
        func: &NamedFunction,
        args: Vec<Expr>,
    ) -> Result<Expr, String> {
        if func.args.len() != args.len() {
            return Err(format!(
                "Expected {} arguments, got {}",
                func.args.len(),
                args.len()
            ));
        }

        // create a new scope for the function
        self.scopes.enter_scope();
        for (i, (arg_name, arg_type)) in func.args.iter().enumerate() {
            let arg = args.get(i).ok_or("Expected an argument")?;
            let arg = self.expect_literal(arg.clone())?;
            self.scopes.new_var(arg_name, arg, arg_type.clone())?;
        }
        let res = self.interpret_expr(func.body.clone())?;
        self.scopes.leave_scope();
        Ok(res)
    }
}
