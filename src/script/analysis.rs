use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::parse::{Block, Conditional, Expression, Statement};
use super::types::{
    EnumType, NO_SENTINEL, Scope, ScopeExt, ScriptValue, SharedScope, SharedSignature, Signature,
    Variable, deobfuscate, well_known_method_arguments,
};

const MAX_ITERATIONS: usize = 10;

pub(super) struct Analyzer {
    made_changes: bool,
    /// Inferred type of each list "slot" — a `(list at index)` element — keyed by
    /// `(list variable name, index variable name)`. This lets a value written into a slot in one
    /// method (`($#SayTable at #n0) = #a`) pick up the type the same slot is later read as in
    /// another (`$Say ($#SayTable at #n0), …` → `Character`). The SAY/MASAY utility methods route
    /// their parameters into typed engine calls through exactly this kind of shared heterogeneous
    /// list, so without it those parameters never get typed. Types are merged with `choose`, so a
    /// slot only ever holds a type both endpoints agree on (a disagreement collapses to `Conflict`,
    /// which never restores a constant) — keeping the "no false constants" property intact.
    slot_types: HashMap<(String, String), EnumType>,
    /// Sentinel `accept` list observed for a slot when it was read as a built-in's `Sentinel`
    /// argument (e.g. `SetSayMotion`'s `0→OFF` motion arg). Propagated onto the parameter written
    /// into that slot so the inferred signature reproduces the sentinel instead of falling back to
    /// the generic `0→NULL`.
    slot_accept: HashMap<(String, String), &'static [i32]>,
}

impl Analyzer {
    pub fn new() -> Self {
        Self {
            made_changes: false,
            slot_types: HashMap::new(),
            slot_accept: HashMap::new(),
        }
    }

    /// Merge a newly-observed type (and any sentinel `accept` list from the reading position) into
    /// a list slot, conservatively (`choose`). Flags a change so the fixpoint keeps iterating.
    fn record_slot(&mut self, key: (String, String), ty: EnumType, accept: &'static [i32]) {
        if !accept.is_empty() && !self.slot_accept.contains_key(&key) {
            self.slot_accept.insert(key.clone(), accept);
            self.made_changes = true;
        }
        let entry = self.slot_types.entry(key).or_insert(EnumType::Any);
        let merged = entry.choose(ty);
        if *entry != merged {
            *entry = merged;
            self.made_changes = true;
        }
    }

    pub fn infer_types(
        &mut self,
        script: &mut Block,
        config: Option<&HashMap<(EnumType, i32), String>>,
        float_config: Option<&HashMap<(EnumType, u32), String>>,
    ) {
        // seed the global scope with the type of every named constant (int and float) so that any
        // script that references one already has its type on hand
        let mut constant_map: HashMap<String, EnumType> = HashMap::new();
        for ((t, _), n) in config.into_iter().flatten() {
            constant_map.insert(n.clone(), *t);
        }
        for ((t, _), n) in float_config.into_iter().flatten() {
            constant_map.insert(n.clone(), *t);
        }
        let constant_map = (!constant_map.is_empty()).then_some(constant_map);
        let global_scope = Scope::new_global(constant_map);
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
        if old_return_type != new_return_type
            && signature.borrow_mut().update_return_type(new_return_type) != old_return_type
        {
            self.made_changes = true;
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
        args: &mut [Expression],
        scope: SharedScope,
    ) {
        let mut prior: Vec<Option<i32>> = Vec::with_capacity(args.len());
        for (i, arg_expr) in args.iter_mut().enumerate() {
            let arg_type = { signature.borrow().arg_type(i) };
            let (final_arg_type, sentinel_accept) = arg_type.resolve(&prior);
            let literal = match arg_expr.unwrap_global().0 {
                &Expression::Int(value) => Some(value),
                _ => None,
            };
            prior.push(literal);

            // a `(list at index)` argument tells us the type stored in that slot (e.g. `$Say` reads
            // its speaker from `($#SayTable at #n0)`, typing that slot `Character`), plus any
            // sentinel behavior of the reading position (`SetSayMotion`'s motion arg is `0→OFF`)
            if let Some(key) = slot_key(arg_expr) {
                self.record_slot(key, final_arg_type, sentinel_accept);
            }

            let (inner_expr, is_global) = arg_expr.unwrap_global_mut();
            match inner_expr {
                Expression::Variable(var) => {
                    self.update(&scope, var, is_global, ScriptValue::Scalar(final_arg_type))
                }
                Expression::FunctionCall(name, args) => {
                    deobfuscate(name);
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
                            ScriptValue::Scalar(_) if args.is_empty() => {
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
                    if let Expression::Variable(obj_var) = obj_expr
                        && let Some(inner_sig) =
                            scope.borrow().lookup_method(obj_var, name, is_global)
                    {
                        self.update_return_type(&inner_sig, final_arg_type);
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
                if let Expression::Variable(var) = left_expr
                    && let Some(value) = get_expression_type(&scope, &*rhs)
                {
                    self.define(&mut scope, var, is_global, value.clone());
                }
            }
            Expression::ReferenceDeclaration(lhs, rhs) => {
                let (left_expr, is_global_var) = lhs.unwrap_global();
                let is_global = is_global_var || is_global;
                if let Expression::Variable(var) = left_expr
                    && let Some(value) = get_expression_type(&scope, &*rhs)
                {
                    self.define(&mut scope, var, is_global, value);
                }
            }
            Expression::MethodCall(var, method, args) => {
                let (obj_expr, is_global_obj) = var.unwrap_global();
                let is_global = is_global_obj || is_global;

                // a method call on a known variable/object pushes argument types from its signature
                let method_sig = if let Expression::Variable(obj_var) = obj_expr {
                    scope.borrow().lookup_method(obj_var, method, is_global)
                } else {
                    None
                };

                if let Some(signature) = method_sig {
                    self.infer_call_types(signature, args, Rc::clone(&scope));
                } else if matches!(
                    method.as_str(),
                    "=" | "<" | ">" | "eq" | "lt" | "le" | "gt" | "ge"
                ) && args.len() == 1
                {
                    // a comparison or assignment unifies the types of its two sides. Either side can
                    // be a variable or a typed call (e.g. `($GetCharDead #x) eq #flag` types `#flag`
                    // Boolean), so we propagate in both directions.
                    let arg_expr = &args[0];

                    // set lhs type based on rhs (only a variable lhs has storage to update)
                    if let Expression::Variable(obj_var) = obj_expr
                        && let Some(arg_type) = get_expression_type(&scope, arg_expr)
                    {
                        self.update(&scope, obj_var, is_global, arg_type);
                    }

                    // set rhs type based on lhs (only a variable rhs has storage to update)
                    let (inner_arg_expr, is_arg_global) = arg_expr.unwrap_global();
                    if let Expression::Variable(arg_var) = inner_arg_expr
                        && let Some(ScriptValue::Scalar(lhs_type)) =
                            get_expression_type(&scope, obj_expr)
                    {
                        self.update(
                            &scope,
                            arg_var,
                            is_arg_global,
                            ScriptValue::Scalar(lhs_type),
                        );
                    }

                    // when the lhs is a list slot `($#list at #idx)`, unify the slot's type with the
                    // rhs variable in both directions — this is how a SAY/MASAY parameter assigned
                    // into `#SayTable` picks up the type that slot is later read as by `$Say`.
                    if let Some(key) = slot_key(obj_expr) {
                        let slot_ty = self.slot_types.get(&key).copied();
                        let slot_accept = self.slot_accept.get(&key).copied();
                        if let Expression::Variable(arg_var) = inner_arg_expr
                            && let Some(slot_ty) = slot_ty
                            && slot_ty.is_concrete()
                        {
                            self.update(
                                &scope,
                                arg_var,
                                is_arg_global,
                                ScriptValue::Scalar(slot_ty),
                            );
                            // carry the slot's sentinel behavior onto the parameter so its
                            // inferred signature reproduces it (value-0 → `#OFF`, not `#NULL`)
                            if let Some(accept) = slot_accept {
                                scope.borrow_mut().update_scalar_sentinel(
                                    arg_var,
                                    is_arg_global,
                                    accept,
                                );
                            }
                        }
                        if let Some(ScriptValue::Scalar(rhs_ty)) =
                            get_expression_type(&scope, arg_expr)
                        {
                            self.record_slot(key, rhs_ty, NO_SENTINEL);
                        }
                    }
                }
            }
            Expression::FunctionCall(name, args) => {
                deobfuscate(name);

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
            let (lhs_expr, is_global) = lhs.unwrap_global_mut();
            if let Expression::Variable(var) = lhs_expr {
                if let Variable(var_name, None) = var {
                    // this may be a global event callback declaration; attempt to deobfuscate
                    deobfuscate(var_name);
                }

                // well-known method signatures are hard-coded by name (e.g. SEL/WEAPONJOIN's first
                // argument is always a Character). Their argument types can't be recovered by
                // following the data flow because the value only ever lands in untyped object
                // attributes, so we seed the signature - which restores the literals at the call
                // sites - but keep the *body's* view of those arguments generic. Letting the seeded
                // type into the body would leak it through the method's internal assignments and
                // comparisons (e.g. WEAPONJOIN stashes its arg in `#Man`, whose `: 0` initializer
                // would then be over-applied to CHID_SHUJINKO) without recovering any real constant.
                let seed = well_known_method_arguments(&var.0);
                let mut func_scope = block.ensure_scope(Rc::clone(&scope));
                let function_sig = match scope.borrow().lookup_function(var, is_global) {
                    Some(callback_sig) => {
                        // if this is a known function, push the types into the function scope
                        for (i, arg_name) in args.iter().enumerate() {
                            let ty = if seed.is_empty() {
                                callback_sig.borrow().arg_type(i).base()
                            } else {
                                EnumType::default()
                            };
                            self.define(
                                &mut func_scope,
                                &arg_name.as_str().into(),
                                false,
                                ScriptValue::Scalar(ty),
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

                if !seed.is_empty() {
                    let mut sig_mut = function_sig.borrow_mut();
                    for (i, &ty) in seed.iter().enumerate() {
                        if sig_mut.infer_argument(i, ty, NO_SENTINEL) {
                            self.made_changes = true;
                        }
                    }
                }

                self.infer_block(block);

                // pull any definitions found in the block up into the signature
                let local_scope = func_scope.borrow_mut();
                let mut sig_mut = function_sig.borrow_mut();
                for (i, arg_name) in args.iter().enumerate() {
                    let inferred = local_scope.lookup_own_scalar(arg_name).unwrap_or_default();
                    let accept = local_scope
                        .lookup_own_scalar_sentinel(arg_name)
                        .unwrap_or(NO_SENTINEL);
                    if sig_mut.infer_argument(i, inferred, accept) {
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
                Statement::WhileLoop(expr, loop_block) => {
                    self.infer_expression(expr, Rc::clone(&block_scope));
                    loop_block.ensure_scope(Rc::clone(&block_scope));
                    self.infer_block(loop_block);
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

/// If `expr` is a list-element access `(list at index)` where both the list and the index are
/// plain (unqualified) variables, return its canonical slot key `(list name, index name)`. The
/// `$`/global prefix is ignored so a write `($#SayTable at #n0)` and a read `($#SayTable at #n0)`
/// in sibling methods map to the same slot. Qualified forms (`$#say#n0`) are deliberately excluded
/// to keep slot identity unambiguous.
fn slot_key(expr: &Expression) -> Option<(String, String)> {
    let (inner, _) = expr.unwrap_global();
    if let Expression::MethodCall(list_expr, method, args) = inner
        && method == "at"
        && args.len() == 1
    {
        let (Expression::Variable(Variable(list_name, None)), _) = list_expr.unwrap_global() else {
            return None;
        };
        let (Expression::Variable(Variable(index_name, None)), _) = args[0].unwrap_global() else {
            return None;
        };
        return Some((list_name.clone(), index_name.clone()));
    }
    None
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
        Expression::TernaryConditional(_, true_expr, false_expr) => {
            let true_type = get_expression_type(scope, true_expr);
            let false_type = get_expression_type(scope, false_expr);
            match (true_type, false_type) {
                (Some(true_type), None) => Some(true_type),
                (None, Some(false_type)) => Some(false_type),
                // the complexity of trying to handle function or object-typed values here is
                // not worth it considering there aren't even any known instances of ternaries in
                // real game scripts
                (Some(ScriptValue::Scalar(true_type)), Some(ScriptValue::Scalar(false_type))) => {
                    Some(ScriptValue::Scalar(true_type.choose(false_type)))
                }
                _ => None,
            }
        }
        Expression::Int(_) | Expression::Float(_) => Some(ScriptValue::Scalar(EnumType::Any)),
        _ => None,
    }
}
