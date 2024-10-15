use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::parse::{Block, Conditional, Expression, Statement};
use super::types::{
    EnumType, Scope, ScopeExt, ScriptValue, SharedScope, SharedSignature, Signature, Variable,
};

const MAX_ITERATIONS: usize = 10;

pub(super) struct Analyzer {
    made_changes: bool,
}

impl Analyzer {
    pub fn new() -> Self {
        Self {
            made_changes: false,
        }
    }

    pub fn infer_types(
        &mut self,
        script: &mut Block,
        config: Option<&HashMap<(EnumType, i32), String>>,
    ) {
        let constant_map: Option<HashMap<_, _>> =
            config.map(|c| c.iter().map(|((t, _), n)| (n.clone(), *t)).collect());
        let (global_scope, _prototype_object) = Scope::new_global(constant_map);
        script.set_scope(global_scope);

        // repeatedly process and infer types until we stop finding anything new
        for _ in 0..MAX_ITERATIONS {
            self.made_changes = false;
            self.infer_block(script);
            if !self.made_changes {
                break;
            }
        }
    }

    fn update_return_type(&mut self, signature: &SharedSignature, new_return_type: EnumType) {
        let old_return_type = { signature.borrow().return_type() };
        if old_return_type != new_return_type {
            if signature.borrow_mut().update_return_type(new_return_type) != old_return_type {
                self.made_changes = true;
            }
        }
    }

    fn check_script_value_changed(
        &mut self,
        old_value: Option<ScriptValue>,
        new_value: Option<ScriptValue>,
    ) {
        match (old_value, new_value) {
            (Some(ScriptValue::Scalar(old_type)), Some(ScriptValue::Scalar(new_type))) => {
                if old_type != new_type {
                    self.made_changes = true;
                }
            }
            (Some(ScriptValue::Function(old_sig)), Some(ScriptValue::Function(new_sig))) => {
                if *old_sig.borrow() != *new_sig.borrow() {
                    self.made_changes = true;
                }
            }
            (Some(ScriptValue::Object(old_scope)), Some(ScriptValue::Object(new_scope))) => {
                if !Rc::ptr_eq(&old_scope, &new_scope) {
                    self.made_changes = true;
                }
            }
            (Some(_), Some(_)) | (Some(_), None) | (None, Some(_)) => {
                self.made_changes = true;
            }
            _ => (),
        }
    }

    fn update(&mut self, scope: &SharedScope, var: &Variable, is_global: bool, value: ScriptValue) {
        let old_value = { scope.borrow().lookup(var, is_global) };
        {
            scope.borrow_mut().update(var, is_global, value);
        }
        let new_value = { scope.borrow().lookup(var, is_global) };
        self.check_script_value_changed(old_value, new_value);
    }

    fn define(
        &mut self,
        scope: &mut SharedScope,
        var: &Variable,
        is_global: bool,
        value: ScriptValue,
    ) {
        let old_value = { scope.borrow().lookup(var, is_global) };
        scope.define(var, is_global, value);
        let new_value = { scope.borrow().lookup(var, is_global) };
        self.check_script_value_changed(old_value, new_value);
    }

    fn infer_call_types(
        &mut self,
        signature: SharedSignature,
        args: &[Expression],
        scope: SharedScope,
    ) {
        let mut select = None;
        for (arg_expr, arg_type) in args.iter().zip(signature.borrow().iter()) {
            if let ((&Expression::Int(value), _), EnumType::Select) =
                (arg_expr.unwrap_global(), arg_type)
            {
                select = Some(value);
                continue;
            }

            let final_arg_type = arg_type.select_type(select);
            let (inner_expr, is_global) = arg_expr.unwrap_global();
            match inner_expr {
                Expression::Variable(var) => {
                    self.update(&scope, var, is_global, ScriptValue::Scalar(final_arg_type))
                }
                Expression::FunctionCall(name, args) => {
                    let name_var = name.as_str().into();
                    // I've seen a few instances of variables (specifically function arguments) being
                    // referenced without a hash, which causes them to be parsed as function calls, so
                    // we need to handle both cases
                    let result = { scope.borrow().lookup(&name_var, is_global) };
                    if let Some(value) = result {
                        match value {
                            ScriptValue::Function(inner_sig) => {
                                self.update_return_type(&inner_sig, final_arg_type);
                            }
                            ScriptValue::Scalar(_) if args.len() == 0 => {
                                self.update(
                                    &scope,
                                    &name_var,
                                    is_global,
                                    ScriptValue::Scalar(final_arg_type),
                                );
                            }
                            _ => (),
                        }
                    }
                }
                Expression::MethodCall(obj_expr, name, _) => {
                    let (obj_expr, is_global_obj) = obj_expr.unwrap_global();
                    let is_global = is_global_obj || is_global;
                    if let Expression::Variable(obj_var) = obj_expr {
                        if let Some(inner_sig) =
                            scope.borrow().lookup_method(obj_var, name, is_global)
                        {
                            self.update_return_type(&inner_sig, final_arg_type);
                        }
                    }
                }
                _ => (),
            }
        }
    }

    fn infer_expression(&mut self, expr: &mut Expression, mut scope: SharedScope) {
        let (expr, is_global) = expr.unwrap_global_mut();

        // do expression-type-specific processing
        match expr {
            Expression::ValueDeclaration(lhs, rhs) => {
                let (left_expr, is_global_var) = lhs.unwrap_global();
                let is_global = is_global_var || is_global;
                if let Expression::Variable(var) = left_expr {
                    if let Some(value) = get_expression_type(&scope, &*rhs) {
                        self.define(&mut scope, var, is_global, value.clone());
                    }
                }
            }
            Expression::ReferenceDeclaration(lhs, rhs) => {
                let (left_expr, is_global_var) = lhs.unwrap_global();
                let is_global = is_global_var || is_global;
                if let Expression::Variable(var) = left_expr {
                    if let Some(value) = get_expression_type(&scope, &*rhs) {
                        self.define(&mut scope, var, is_global, value);
                    }
                }
            }
            Expression::MethodCall(var, method, args) => {
                let (obj_expr, is_global_obj) = var.unwrap_global();
                let is_global = is_global_obj || is_global;
                if let Expression::Variable(obj_var) = obj_expr {
                    // this block is necessary to ensure the borrow is dropped promptly
                    let result = { scope.borrow().lookup_method(obj_var, method, is_global) };

                    if let Some(signature) = result {
                        self.infer_call_types(signature, args, Rc::clone(&scope));
                    } else if matches!(
                        method.as_str(),
                        "=" | "<" | ">" | "eq" | "lt" | "le" | "gt" | "ge"
                    ) && args.len() == 1
                    {
                        let arg_expr = &args[0];

                        // set lhs type based on rhs
                        if let Some(arg_type) = get_expression_type(&scope, arg_expr) {
                            self.update(&scope, obj_var, is_global, arg_type);
                        }

                        if method == "=" && obj_var.0 == "id" {
                            println!("break here");
                        }

                        // set rhs type based on lhs
                        let result = { scope.borrow().lookup(obj_var, is_global) };
                        let (inner_arg_expr, is_arg_global) = arg_expr.unwrap_global();
                        if let (
                            Some(ScriptValue::Scalar(lhs_type)),
                            Expression::Variable(arg_var),
                        ) = (result, inner_arg_expr)
                        {
                            self.update(
                                &scope,
                                arg_var,
                                is_arg_global,
                                ScriptValue::Scalar(lhs_type),
                            );
                        }
                    }
                }
            }
            Expression::FunctionCall(name, args) => {
                // this block is necessary to ensure the borrow is dropped promptly
                let result = {
                    scope
                        .borrow()
                        .lookup_function(&name.as_str().into(), is_global)
                };

                if let Some(signature) = result {
                    self.infer_call_types(signature, args, Rc::clone(&scope));
                }
            }
            _ => (),
        }

        // continue down the AST
        if let Some((lhs, Expression::FunctionDefinition(args, block))) = expr.declaration_mut() {
            let (lhs_expr, is_global) = lhs.unwrap_global();
            if let Expression::Variable(var) = lhs_expr {
                let mut func_scope = block.ensure_scope(Rc::clone(&scope));
                let function_sig = match scope.borrow().lookup_function(var, is_global) {
                    Some(callback_sig) => {
                        // if this is a known function, push the types into the function scope
                        for (arg_name, arg_type) in args.iter().zip(callback_sig.borrow().iter()) {
                            self.define(
                                &mut func_scope,
                                &arg_name.as_str().into(),
                                false,
                                ScriptValue::Scalar(arg_type),
                            );
                        }
                        callback_sig
                    }
                    None => {
                        // push generic definitions into the function scope just so we know they're local
                        for arg_name in args.iter() {
                            self.define(
                                &mut func_scope,
                                &arg_name.as_str().into(),
                                false,
                                ScriptValue::Scalar(EnumType::default()),
                            );
                        }
                        Rc::new(RefCell::new(Signature::args(vec![
                            EnumType::default();
                            args.len()
                        ])))
                    }
                };

                self.infer_block(block);

                // pull any definitions found in the block up into the signature
                let local_scope = func_scope.borrow_mut();
                let mut sig_mut = function_sig.borrow_mut();
                for (i, arg_name) in args.iter().enumerate() {
                    let old_type = sig_mut.get_argument(i);
                    let new_type = sig_mut.add_argument(
                        i,
                        local_scope.lookup_own_scalar(arg_name).unwrap_or_default(),
                    );
                    if old_type != new_type {
                        self.made_changes = true;
                    }
                }
            }
        } else {
            // generically process any inner blocks (although there shouldn't be any, because the above case
            // should handle all that occur in practice)
            for (_, block) in expr.inner_blocks_mut() {
                block.ensure_scope(Rc::clone(&scope));
                self.infer_block(block);
            }
        }

        // walk the AST to explore any sub-expressions
        expr.walk_mut(&mut |e| {
            self.infer_expression(e, Rc::clone(&scope));
        });
    }

    fn infer_block(&mut self, block: &mut Block) {
        let block_scope = block.scope().unwrap();
        for stmt in block.iter_mut() {
            match stmt {
                Statement::ObjectInitialization(expr, init_block) => {
                    self.infer_expression(expr, Rc::clone(&block_scope));
                    let (expr, mut is_global) = expr.unwrap_global();
                    let var = match expr {
                        Expression::Variable(var) => Some(var),
                        Expression::ReferenceDeclaration(lhs, _)
                        | Expression::ValueDeclaration(lhs, _) => {
                            let (expr, is_inner_global) = lhs.unwrap_global();
                            if let Expression::Variable(var) = expr {
                                is_global = is_inner_global;
                                Some(var)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    match var.and_then(|v| block_scope.borrow().lookup_object(v, is_global)) {
                        Some(scope) => {
                            init_block.set_scope(scope);
                        }
                        None => {
                            // FIXME: this is really probably an error
                            init_block.ensure_scope(Rc::clone(&block_scope));
                        }
                    }
                    self.infer_block(init_block);
                }
                Statement::Conditional(conditional, else_block) => {
                    let mut condition = Some(conditional);
                    while let Some(Conditional(expr, condition_block, next_condition)) = condition {
                        self.infer_expression(expr, Rc::clone(&block_scope));
                        condition_block.ensure_scope(Rc::clone(&block_scope));
                        self.infer_block(condition_block);
                        condition = next_condition.as_deref_mut();
                    }
                    if let Some(else_block) = else_block {
                        else_block.ensure_scope(Rc::clone(&block_scope));
                        self.infer_block(else_block);
                    }
                }
                Statement::Expression(expr) => {
                    self.infer_expression(expr, Rc::clone(&block_scope));
                }
                _ => (),
            }
        }
    }
}

fn get_expression_type(scope: &SharedScope, expr: &Expression) -> Option<ScriptValue> {
    let (inner_expr, is_global) = expr.unwrap_global();
    match inner_expr {
        Expression::Variable(var) => scope.borrow().lookup(var, is_global),
        Expression::FunctionCall(name, _) => scope
            .borrow()
            .lookup_function(&name.as_str().into(), is_global)
            .map(|s| s.borrow().return_type())
            .map(ScriptValue::Scalar),
        Expression::MethodCall(obj_expr, method, _) => {
            let (obj_expr, is_global_obj) = obj_expr.unwrap_global();
            let is_global = is_global_obj || is_global;
            if let Expression::Variable(obj_var) = obj_expr {
                scope
                    .borrow()
                    .lookup_method(obj_var, method, is_global)
                    .map(|s| ScriptValue::Scalar(s.borrow().return_type()))
            } else {
                None
            }
        }
        Expression::FunctionDefinition(args, _) => Some(ScriptValue::Function(Rc::new(
            RefCell::new(Signature::args(vec![EnumType::default(); args.len()])),
        ))),
        Expression::Int(_) => Some(ScriptValue::Scalar(EnumType::Any)),
        _ => None,
    }
}
