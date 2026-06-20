use std::collections::HashMap;

use anyhow::Result;
use regex::Regex;

mod analysis;
mod parse;
mod types;

use analysis::Analyzer;
use parse::{Block, Conditional, Expression, Statement};
use types::{EnumType, NO_SENTINEL, ScriptValue, SharedScope, SharedSignature, Variable};

fn start_line(
    line_start: &mut bool,
    s: &mut String,
    indentation_level: i32,
    tab_width: Option<usize>,
) {
    if *line_start {
        s.push('\n');
        for _ in 0..indentation_level {
            if let Some(num_spaces) = tab_width {
                for _ in 0..num_spaces {
                    s.push(' ');
                }
            } else {
                s.push('\t');
            }
        }
        *line_start = false;
    }
}

/// Format a script for readability.
///
/// Converts the script from Shift JIS to UTF-8 and adds newlines and indentation at appropriate points.
///
/// # Arguments
///
/// * `text` - The script text
/// * `tab_width` - If None, the script will be indented with tabs. Otherwise, it will be indented with
///   this many spaces per indentation level.
///
/// # Returns
///
/// The formatted script as a UTF-8 string.
pub fn format_script<T: AsRef<str>>(text: T, tab_width: Option<usize>) -> String {
    let text = text.as_ref();
    let mut output = String::with_capacity(text.len());

    let mut in_string = false;
    let mut line_start = false;
    let mut block_start = false;
    let mut indentation_level = 0;
    // skip whitespace at the beginning of the file
    for c in text.chars().skip_while(|c| matches!(c, ' ' | '\t' | '\n')) {
        match c {
            '"' => {
                start_line(&mut line_start, &mut output, indentation_level, tab_width);

                in_string = !in_string; // FIXME: do the scripts allow escapes?
                output.push('"');
                block_start = false;
            }
            ';' if !in_string => {
                start_line(&mut line_start, &mut output, indentation_level, tab_width);

                output.push(';');
                line_start = true;
                block_start = false;
            }
            '{' if !in_string => {
                start_line(&mut line_start, &mut output, indentation_level, tab_width);

                output.push('{');
                line_start = true;
                block_start = true;
                indentation_level += 1;
            }
            '}' if !in_string => {
                indentation_level -= 1;
                // don't start a new line if the block is empty
                if block_start {
                    output.push(' ');
                } else {
                    start_line(&mut line_start, &mut output, indentation_level, tab_width);
                }
                output.push('}');
                line_start = false;
                block_start = false;
            }
            ' ' | '\t' | '\n' if !in_string => {
                if !line_start {
                    output.push(c);
                }
            }
            _ if !in_string && line_start => {
                start_line(&mut line_start, &mut output, indentation_level, tab_width);
                output.push(c);
                block_start = false;
            }
            _ => {
                output.push(c);
                block_start = false;
            }
        }
    }

    output
}

/// Minify a previously-formatted script for storage in volume.dat.
///
/// Removes newlines and indentation and collapses whitespace.
///
/// # Arguments
///
/// * `script` - The formatted script text
///
/// # Returns
///
/// The minified script
pub fn unformat_script(script: &str) -> String {
    let mut minified = String::with_capacity(script.len());
    let mut in_string = false;
    let mut in_space = false;
    for c in script.chars() {
        match c {
            '"' => {
                minified.push('"');
                in_string = !in_string;
                in_space = false;
            }
            ' ' | '\t' | '\n' if !in_string => {
                if !in_space {
                    minified.push(' ');
                    in_space = true;
                }
            }
            _ => {
                minified.push(c);
                in_space = false;
            }
        }
    }

    minified
}

#[derive(Debug, Clone)]
pub struct ScriptFormatter {
    config: Option<HashMap<(EnumType, i32), String>>,
    // float-valued constants are keyed by the f32 bit pattern, since f32 is neither Hash nor Eq
    float_config: Option<HashMap<(EnumType, u32), String>>,
    made_changes: bool,
    quiet: bool,
    // whether we're lexically inside an `@{}` object-attribute block (including nested method
    // bodies). The developers prefix constants there with `$#` ~2/3 of the time, so as a structural
    // approximation (Rule C) we emit restored constants as `$#NAME` whenever this is set.
    in_attribute: bool,
}

impl ScriptFormatter {
    pub fn new() -> Self {
        Self {
            config: None,
            float_config: None,
            made_changes: false,
            quiet: false,
            in_attribute: false,
        }
    }

    pub fn set_quiet(&mut self, quiet: bool) {
        self.quiet = quiet;
    }

    fn reset(&mut self) {
        self.made_changes = false;
        self.in_attribute = false;
    }

    fn get_constant(
        &self,
        value_type: EnumType,
        value: i32,
        accept: &[i32],
        reject: &[i32],
    ) -> Option<Expression> {
        if !value_type.is_concrete() {
            return None;
        }

        let config = self.config.as_ref()?;
        // when this value is sentinel-eligible, a generic INIT/ON/OFF constant of the same value
        // wins over a type-specific constant that happens to share that value
        if accept.contains(&value) {
            let generic = match value {
                -1 => config.get(&(EnumType::Initialize, -1)),
                0 => config.get(&(EnumType::Boolean, 0)), // OFF
                1 => config.get(&(EnumType::Boolean, 1)), // ON
                _ => None,
            };
            if let Some(name) = generic {
                return Some(Expression::new_var(name.clone()));
            }
        }
        config
            .get(&(value_type, value))
            // a rejected value is a deliberate literal at this position, so skip the generic
            // INIT/NULL fallback that would otherwise apply when there's no type-specific constant
            .or_else(|| {
                if reject.contains(&value) {
                    return None;
                }
                match value {
                    -1 => config.get(&(EnumType::Initialize, -1)),
                    0 => config.get(&(EnumType::Null, 0)),
                    _ => None,
                }
            })
            .map(|s| Expression::new_var(s.clone()))
    }

    /// Look up the symbolic constant for a float-valued argument of the given type, if any.
    fn get_float_constant(&self, value_type: EnumType, value: f32) -> Option<Expression> {
        if !value_type.is_concrete() {
            return None;
        }

        self.float_config
            .as_ref()?
            .get(&(value_type, value.to_bits()))
            .map(|s| Expression::new_var(s.clone()))
    }

    fn use_constant(
        &mut self,
        value_type: EnumType,
        expr: &mut Expression,
        accept: &[i32],
        reject: &[i32],
        in_assignment: bool,
    ) {
        if !value_type.is_concrete() {
            return;
        }

        // coordinate families are only restored where the developer routed the value through a
        // named variable (an assignment/declaration). Inline, a number at a coordinate position is
        // almost always a literal position - including whole numbers written as ints (e.g. a `0`
        // coordinate, which would otherwise wrongly resolve to NULL via the generic int fallback).
        // The exception is an explicit sentinel value (e.g. SetPosLineAction's `-1`/INIT clear
        // form), which is a flag rather than a position and should still be restored inline.
        if value_type.is_coordinate() && !in_assignment {
            let is_sentinel =
                matches!(expr.unwrap_global().0, &Expression::Int(v) if accept.contains(&v));
            if !is_sentinel {
                return;
            }
        }

        let constant = match expr.unwrap_global().0 {
            &Expression::Int(value) => match self.get_constant(value_type, value, accept, reject) {
                found @ Some(_) => found,
                None => {
                    // a rejected value is an intentional literal, so don't flag it as unexpected
                    if !self.quiet && !reject.contains(&value) {
                        println!(
                            "Warning: unexpected value {} for type {:?}",
                            value, value_type,
                        );
                    }
                    None
                }
            },
            // most float literals are genuine coordinates rather than constants, so a miss here is
            // expected and we silently leave the literal in place instead of warning
            &Expression::Float(value) => self.get_float_constant(value_type, value),
            _ => return,
        };

        // if we found a match for a symbolic constant, replace the literal expression with one
        // referencing the constant. Inside an `@{}` block the developers conventionally prefix
        // constants with `$#`, so wrap it in a `Global` (which renders as `$`) to match (Rule C).
        if let Some(constant) = constant {
            *expr = if self.in_attribute {
                Expression::Global(Box::new(constant))
            } else {
                constant
            };
            self.made_changes = true;
        }
    }

    fn process_call(&mut self, args: &mut [Expression], signature: &SharedSignature) {
        let mut prior: Vec<Option<i32>> = Vec::with_capacity(args.len());
        for (i, arg_expr) in args.iter_mut().enumerate() {
            let arg_type = { signature.borrow().arg_type(i) };
            let (resolved, accept, reject) = arg_type.resolve(&prior);
            // record this argument's literal value before it may be replaced with a constant
            prior.push(match arg_expr.unwrap_global().0 {
                &Expression::Int(value) => Some(value),
                _ => None,
            });

            // inline call arguments are never an assignment context
            self.use_constant(resolved, arg_expr, accept, reject, false);
        }
    }

    /// Resolve the type/value of an expression used as the receiver of a method call or comparison:
    /// a variable's stored value, or the return type of a function/method call. This lets a
    /// comparison like `($GetCharDead #x) eq 0` propagate the call's `Boolean` return type to the
    /// literal on the other side, not just plain `#var eq 0` comparisons.
    fn resolve_value(
        &self,
        expr: &Expression,
        scope: &SharedScope,
        is_global: bool,
    ) -> Option<ScriptValue> {
        let (inner, is_global_inner) = expr.unwrap_global();
        let is_global = is_global || is_global_inner;
        match inner {
            Expression::Variable(var) => scope.borrow().lookup(var, is_global),
            Expression::FunctionCall(name, _, _) => scope
                .borrow()
                .lookup_function(&name.as_str().into(), is_global)
                .map(ScriptValue::Function),
            Expression::MethodCall(obj_expr, method, _) => {
                let (obj_expr, is_global_obj) = obj_expr.unwrap_global();
                if let Expression::Variable(obj_var) = obj_expr {
                    scope
                        .borrow()
                        .lookup_method(obj_var, method, is_global || is_global_obj)
                        .map(ScriptValue::Function)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn process_method(&mut self, object: &ScriptValue, method: &str, args: &mut [Expression]) {
        match (args.len(), method, object) {
            // if this is a comparison or assignment to a scalar with a single argument
            (1, "eq" | "lt" | "le" | "gt" | "ge" | "<" | ">" | "=", _) => {
                // only `=` (and the declarations below) is an assignment; the others are comparisons
                self.use_constant(object.get_type(), &mut args[0], NO_SENTINEL, NO_SENTINEL, method == "=");
            }
            (_, _, ScriptValue::Object(scope)) => {
                if let Some(sig) = scope.borrow().lookup_own_function(method) {
                    self.process_call(args, &sig);
                }
            }
            _ => (),
        }
    }

    fn process_expression(&mut self, expr: &mut Expression, scope: &SharedScope) {
        let (expr, is_global) = expr.unwrap_global_mut();

        // do expression-type-specific processing
        match expr {
            Expression::MethodCall(var, method, args) => {
                let (obj_expr, is_global_obj) = var.unwrap_global();
                if let Some(obj) = self.resolve_value(obj_expr, scope, is_global || is_global_obj) {
                    self.process_method(&obj, method, args);
                }
            }
            Expression::FunctionCall(name, args, _) => {
                if let Some(sig) = scope
                    .borrow()
                    .lookup_function(&name.as_str().into(), is_global)
                {
                    self.process_call(args, &sig);
                }
            }
            Expression::ReferenceDeclaration(lhs, rhs) | Expression::ValueDeclaration(lhs, rhs) => {
                if let (Expression::Variable(var), is_global_var) = lhs.unwrap_global()
                    && let Some(obj) = scope.borrow().lookup(var, is_global || is_global_var)
                {
                    // a declaration is an assignment context
                    self.use_constant(obj.get_type(), rhs, NO_SENTINEL, NO_SENTINEL, true);
                }
            }
            _ => (),
        }

        // continue down the AST

        // process any function definitions that occur in this expression
        for (_, inner_block) in expr.inner_blocks_mut() {
            self.process_block(inner_block);
        }

        // walk the AST to explore any sub-expressions
        expr.walk_mut(&mut |e| {
            self.process_expression(e, scope);
        });
    }

    fn process_block(&mut self, block: &mut Block) {
        let scope = block.scope().unwrap();
        for stmt in block.iter_mut() {
            match stmt {
                Statement::ObjectInitialization(expr, init_block) => {
                    // the object expression itself is outside the `@{}`; only its body is inside
                    self.process_expression(expr, &scope);
                    let was_in_attribute = self.in_attribute;
                    self.in_attribute = true;
                    self.process_block(init_block);
                    self.in_attribute = was_in_attribute;
                }
                Statement::Conditional(conditional, else_block) => {
                    let mut condition = Some(conditional);
                    while let Some(Conditional(expr, condition_block, next_condition)) = condition {
                        self.process_expression(expr, &scope);
                        self.process_block(condition_block);
                        condition = next_condition.as_deref_mut();
                    }
                    if let Some(else_block) = else_block {
                        self.process_block(else_block);
                    }
                }
                Statement::Expression(expr) => {
                    self.process_expression(expr, &scope);
                }
                _ => (),
            }
        }
    }

    pub fn use_config<T: AsRef<str>>(&mut self, script: T) -> Result<()> {
        let parsed = parse::parse(script)?;
        let mut map = HashMap::new();
        let mut float_map = HashMap::new();
        let declarations = parsed.into_iter().filter_map(|s| match s {
            Statement::Expression(e) => e.into_declaration(),
            _ => None,
        });
        for (name_expr, value_expr) in declarations {
            let Expression::Variable(Variable(name, None)) = name_expr else {
                continue;
            };

            let Some(constant_type) = EnumType::get_constant_type(&name) else {
                continue;
            };

            match value_expr {
                Expression::Int(value) => {
                    map.insert((constant_type, value), name);
                }
                Expression::Float(value) => {
                    float_map.insert((constant_type, value.to_bits()), name);
                }
                _ => continue,
            }
        }

        self.config = Some(map);
        self.float_config = Some(float_map);
        Ok(())
    }

    pub fn format_script<T: AsRef<str>>(
        &mut self,
        script: T,
        tab_width: Option<usize>,
    ) -> Result<String> {
        self.reset();

        let mut block = parse::parse(script)?;
        if self.config.is_some() || self.float_config.is_some() {
            let mut analyzer = Analyzer::new();
            analyzer.infer_types(&mut block, self.config.as_ref(), self.float_config.as_ref());
            self.process_block(&mut block);
        }
        let text = block.to_string_top_level();
        Ok(match tab_width {
            Some(num_spaces) => text.replace('\t', " ".repeat(num_spaces).as_str()),
            None => text,
        })
    }

    pub fn unformat_script<T: AsRef<str>>(&self, script: T) -> Result<String> {
        if self.config.is_some() {
            let mut block = parse::parse(script)?;
            if block.is_empty() {
                return Ok(String::new());
            }

            if let Statement::Expression(Expression::Global(ref expr)) = block[0]
                && let Expression::FunctionCall(ref name, ref args, _) = **expr
                && name == "Include"
                && args.len() == 1
                && let Expression::String(ref arg) = args[0]
                && arg == "config.h"
            {
                // remove the config.h include
                block.remove(0);
            }

            let mut text = block.to_string_top_level();
            for ((_, value), name) in self.config.as_ref().unwrap().iter() {
                let re = Regex::new(&format!("\\$#{}\\b", name))?;
                let string_value = value.to_string();
                text = re.replace_all(&text, string_value.as_str()).into_owned();
            }

            Ok(unformat_script(text.as_str()))
        } else {
            Ok(unformat_script(script.as_ref()))
        }
    }
}

impl Default for ScriptFormatter {
    fn default() -> Self {
        Self::new()
    }
}

/// Type-inference scoring harness (Step 0 of plan.md).
///
/// Measures how accurately the formatter restores the symbolic constants the original
/// developers used, using the PSP release (constants intact) as ground truth.
///
/// Methodology — a self-referential round-trip that isolates inference from all other noise:
///   * `reference` = current_formatter(ground_truth, no config) — the devs' real constants,
///     formatted by the *current* code.
///   * `ours`      = current_formatter(strip_constants(ground_truth), config) — what our
///     inference restores from a fully literal (preprocessed-equivalent) input.
/// Because both sides run through the same formatter on identical logic, their token streams
/// align 1:1 and the only differences are constant-vs-literal at each position. This removes
/// inter-version logic changes and formatter-version differences from the metric.
///
/// Run on demand (it needs the external corpus and is slow, so it's `#[ignore]`d):
///   SAMURAI_SCRIPTS_DIR=/path/to/samurai_scripts cargo test --release scorecard -- --ignored --nocapture
#[cfg(test)]
mod scorecard {
    use std::collections::HashMap;
    use std::path::PathBuf;

    use regex::Regex;
    use walkdir::WalkDir;

    use super::ScriptFormatter;
    use super::types::EnumType;

    struct Config {
        /// Mirrors `ScriptFormatter::use_config`: only int-valued, typed constants.
        int_map: HashMap<(EnumType, i32), String>,
        /// The float-valued counterpart, keyed by f32 bit pattern.
        float_map: HashMap<(EnumType, u32), String>,
        /// Every named define (int and float) -> its literal text, for stripping.
        value_text: HashMap<String, String>,
        /// Every named define -> its numeric value, for same-value comparisons.
        value_num: HashMap<String, f64>,
    }

    /// Parse config.h leniently, line by line, so a malformed line (e.g. the unterminated
    /// `( MTASG_BASIC )` on line 33) doesn't abort the whole load the way the real parser does.
    fn load_config(path: &std::path::Path) -> Config {
        let text = String::from_utf8_lossy(&std::fs::read(path).expect("read config.h")).into_owned();
        let line_re = Regex::new(r"(?m)^\s*#([A-Za-z_][A-Za-z0-9_]*)\s*\|\s*(-?\d+(?:\.\d+)?)\s*;").unwrap();
        let mut int_map = HashMap::new();
        let mut float_map = HashMap::new();
        let mut value_text = HashMap::new();
        let mut value_num = HashMap::new();
        for caps in line_re.captures_iter(&text) {
            let name = caps[1].to_string();
            let val_str = caps[2].to_string();
            let num: f64 = val_str.parse().unwrap();
            value_num.insert(name.clone(), num);
            // last write wins, matching HashMap insertion order in use_config
            if let Some(t) = EnumType::get_constant_type(&name) {
                if val_str.contains('.') {
                    if let Ok(fval) = val_str.parse::<f32>() {
                        float_map.insert((t, fval.to_bits()), name.clone());
                    }
                } else if let Ok(ival) = val_str.parse::<i32>() {
                    int_map.insert((t, ival), name.clone());
                }
            }
            value_text.insert(name, val_str);
        }
        Config { int_map, float_map, value_text, value_num }
    }

    /// Replace every `$?#NAME` config-constant reference with its literal value, leaving strings,
    /// non-constant variables, and all other tokens (and whitespace) untouched.
    fn strip_constants(text: &str, cfg: &Config) -> String {
        let re = Regex::new(r#""[^"]*"|\$?#[A-Za-z_][A-Za-z0-9_]*"#).unwrap();
        re.replace_all(text, |caps: &regex::Captures| {
            let m = &caps[0];
            if m.starts_with('"') {
                return m.to_string();
            }
            let name = m.trim_start_matches('$').trim_start_matches('#');
            match cfg.value_text.get(name) {
                Some(v) => v.clone(),
                None => m.to_string(),
            }
        })
        .into_owned()
    }

    fn tokenize(text: &str) -> Vec<String> {
        let re = Regex::new(r#"\$?#?[A-Za-z_][A-Za-z0-9_]*|-?\d+\.\d+|-?\d+|"[^"]*"|\S"#).unwrap();
        re.find_iter(text).map(|m| m.as_str().to_string()).collect()
    }

    /// strip the optional global `$` prefix
    fn undollar(tok: &str) -> &str {
        tok.strip_prefix('$').unwrap_or(tok)
    }

    /// constant name if this token references a known config constant, else None
    fn const_name<'a>(tok: &'a str, cfg: &Config) -> Option<&'a str> {
        let name = undollar(tok).strip_prefix('#')?;
        cfg.value_text.contains_key(name).then_some(name)
    }

    fn is_number(tok: &str) -> bool {
        let t = undollar(tok);
        !t.is_empty() && t.bytes().next().map(|b| b == b'-' || b.is_ascii_digit()).unwrap_or(false)
            && t.bytes().all(|b| b == b'-' || b == b'.' || b.is_ascii_digit())
    }

    /// approximate "enclosing call": nearest preceding bare identifier (a function/method
    /// name), skipping `#`-prefixed variables/constants, operators, and method keywords.
    fn func_of(tokens: &[String], idx: usize) -> String {
        for t in tokens[..idx].iter().rev() {
            let u = undollar(t);
            if u.starts_with('#') {
                continue; // variable or constant, not a call name
            }
            if u.chars().next().map(|c| c.is_ascii_alphabetic()).unwrap_or(false)
                && !matches!(u, "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "and" | "or" | "not" | "at" | "add" | "sub" | "mul" | "div" | "list")
            {
                return u.to_string();
            }
        }
        "?".to_string()
    }

    #[derive(Default)]
    struct Counts {
        // denominator: positions where the dev used a config constant
        ref_constants: usize,
        correct: usize,
        missed: usize,       // ours = bare literal (inference produced nothing)
        missed_float: usize, // subset of missed where the true constant is float-valued
        sentinel: usize,     // ours = a different constant with the SAME value (A)
        wrong: usize,        // ours = a different constant with a DIFFERENT value (B)
        over: usize,         // ref = literal but ours = constant (over-application)
        structural: usize,   // unexpected misalignment at this position
        ref_dollar: usize,   // ref constant carried a `$` prefix
        dollar_match: usize, // correct positions where our `$`-prefix matches the ref's (Rule C)
    }

    fn topn(map: &HashMap<String, usize>, n: usize) -> Vec<(String, usize)> {
        let mut v: Vec<_> = map.iter().map(|(k, c)| (k.clone(), *c)).collect();
        v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        v.truncate(n);
        v
    }

    fn family(name: &str) -> String {
        name.split('_').next().unwrap_or(name).to_string()
    }

    /// Recursively splice `$Include "x.sol"` directives by replacing each with the (also
    /// include-resolved) contents of the referenced file, mirroring the *inlined* form the
    /// shipped/preprocessed scripts take in production. The PSP corpus, by contrast, keeps
    /// includes un-inlined, so without this the per-file scoring never sees utility-class method
    /// bodies (ClassSAY, ClassMOVE, …) that live in sibling files — making any cross-file
    /// inference untestable. Resolution is relative to each file's own directory. `config.h` and
    /// non-`.sol`/`.lst` includes are left as literal directives; missing files are skipped. A
    /// canonical-path visited set dedupes repeated includes and breaks cycles.
    fn resolve_includes(path: &std::path::Path) -> String {
        fn go(
            path: &std::path::Path,
            inc_re: &Regex,
            visited: &mut std::collections::HashSet<PathBuf>,
            out: &mut String,
        ) {
            let canon = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
            if !visited.insert(canon) {
                return; // already inlined somewhere in this unit (dedupe / cycle guard)
            }
            let text = match std::fs::read(path) {
                Ok(bytes) => String::from_utf8_lossy(&bytes).into_owned(),
                Err(_) => return,
            };
            let dir = path.parent().map(PathBuf::from).unwrap_or_default();
            for line in text.lines() {
                if let Some(caps) = inc_re.captures(line) {
                    let name = &caps[1];
                    if name.ends_with(".sol") || name.ends_with(".lst") {
                        go(&dir.join(name), inc_re, visited, out);
                        continue;
                    }
                }
                out.push_str(line);
                out.push('\n');
            }
        }

        let inc_re = Regex::new(r#"^\s*\$Include\s+"([^"]+)"\s*;\s*$"#).unwrap();
        let mut visited = std::collections::HashSet::new();
        let mut out = String::new();
        go(path, &inc_re, &mut visited, &mut out);
        out
    }

    #[test]
    #[ignore = "needs the external samurai_scripts corpus; run explicitly with --ignored"]
    fn scorecard() {
        let dir = PathBuf::from(std::env::var("SAMURAI_SCRIPTS_DIR").expect("SAMURAI_SCRIPTS_DIR env var to be set"));
        let cfg = load_config(&dir.join("config.h"));
        eprintln!(
            "loaded config: {} typed-int constants, {} total named defines",
            cfg.int_map.len(),
            cfg.value_text.len()
        );

        let mut c = Counts::default();
        let mut parse_errors = 0usize;
        let mut structural_files = 0usize;
        let mut files = 0usize;
        let mut missed_family: HashMap<String, usize> = HashMap::new();
        let mut missed_func: HashMap<String, usize> = HashMap::new();
        let mut sentinel_pair: HashMap<String, usize> = HashMap::new(); // "ref->our" by family
        let mut sentinel_func: HashMap<String, usize> = HashMap::new();
        let mut wrong_func: HashMap<String, usize> = HashMap::new();
        let mut over_func: HashMap<String, usize> = HashMap::new();

        let mut paths: Vec<_> = WalkDir::new(dir.join("samurai"))
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| {
                let p = e.path();
                p.is_file()
                    && matches!(p.extension().and_then(|s| s.to_str()), Some("sol") | Some("lst"))
            })
            .map(|e| e.path().to_path_buf())
            .collect();
        paths.sort();

        for path in &paths {
            // inline `$Include`s so utility-class method bodies are in scope, matching the
            // pre-processed (inlined) form the formatter targets in production
            let text = resolve_includes(path);

            // reference: format ground truth as-is (constants preserved), no inference
            let mut ref_fmt = ScriptFormatter::new();
            ref_fmt.set_quiet(true);
            let reference = match ref_fmt.format_script(&text, None) {
                Ok(s) => s,
                Err(_) => {
                    parse_errors += 1;
                    continue;
                }
            };

            // ours: strip constants to literals, then run real inference
            let literal = strip_constants(&text, &cfg);
            let mut our_fmt = ScriptFormatter::new();
            our_fmt.set_quiet(true);
            our_fmt.config = Some(cfg.int_map.clone());
            our_fmt.float_config = Some(cfg.float_map.clone());
            let ours = match our_fmt.format_script(&literal, None) {
                Ok(s) => s,
                Err(_) => {
                    parse_errors += 1;
                    continue;
                }
            };

            let rt = tokenize(&reference);
            let ot = tokenize(&ours);
            files += 1;
            if rt.len() != ot.len() {
                structural_files += 1;
                continue;
            }

            for i in 0..rt.len() {
                let (r, o) = (&rt[i], &ot[i]);
                let rname = const_name(r, &cfg);
                let oname = const_name(o, &cfg);

                if let Some(rn) = rname {
                    c.ref_constants += 1;
                    if r.starts_with('$') {
                        c.ref_dollar += 1;
                    }
                    if undollar(r) == undollar(o) {
                        c.correct += 1;
                        // among positions where we restored the right constant, does our `$`-prefix
                        // (emitted by Rule C inside `@{}`) match the developer's?
                        if r.starts_with('$') == o.starts_with('$') {
                            c.dollar_match += 1;
                        }
                        continue;
                    }
                    if is_number(o) {
                        c.missed += 1;
                        if cfg.value_num.get(rn).map(|v| v.fract() != 0.0).unwrap_or(false) {
                            c.missed_float += 1;
                        }
                        *missed_family.entry(family(rn)).or_default() += 1;
                        *missed_func.entry(func_of(&rt, i)).or_default() += 1;
                    } else if let Some(on) = oname {
                        let same = cfg.value_num.get(rn) == cfg.value_num.get(on);
                        if same {
                            c.sentinel += 1;
                            *sentinel_pair.entry(format!("{}->{}", family(rn), family(on))).or_default() += 1;
                            *sentinel_func.entry(func_of(&rt, i)).or_default() += 1;
                        } else {
                            c.wrong += 1;
                            *wrong_func.entry(func_of(&rt, i)).or_default() += 1;
                        }
                    } else {
                        c.structural += 1;
                    }
                } else if let Some(on) = oname.filter(|_| is_number(r)) {
                    c.over += 1;
                    *over_func.entry(format!("{} [{}]", func_of(&ot, i), family(on))).or_default() += 1;
                } else if undollar(r) != undollar(o) {
                    c.structural += 1;
                }
            }
        }

        let pct = |n: usize| if c.ref_constants == 0 { 0.0 } else { 100.0 * n as f64 / c.ref_constants as f64 };
        println!("\n==================== INFERENCE SCORECARD ====================");
        println!("files scored: {files}   parse errors: {parse_errors}   structural-mismatch files (skipped): {structural_files}");
        println!("\nconstant positions (denominator): {}", c.ref_constants);
        println!("  correct        : {:7}  ({:5.2}%)   <-- headline accuracy", c.correct, pct(c.correct));
        println!("  missed (C)     : {:7}  ({:5.2}%)   left a literal; of which float: {} ({:.2}%)", c.missed, pct(c.missed), c.missed_float, pct(c.missed_float));
        println!("  sentinel (A)   : {:7}  ({:5.2}%)   wrong const, SAME value (conditional/sentinel)", c.sentinel, pct(c.sentinel));
        println!("  wrong (B)      : {:7}  ({:5.2}%)   wrong const, DIFFERENT value", c.wrong, pct(c.wrong));
        println!("  structural     : {:7}  ({:5.2}%)", c.structural, pct(c.structural));
        println!("over-application : {:7}              produced a constant where dev wrote a literal", c.over);
        println!("\n$-prefix (cosmetic, excluded from accuracy above): {} of {} ref constants carried `$` ({:.2}%).", c.ref_dollar, c.ref_constants, pct(c.ref_dollar));
        let dollar_pct = if c.correct == 0 { 0.0 } else { 100.0 * c.dollar_match as f64 / c.correct as f64 };
        println!("  prefix accuracy (over {} correctly-restored positions): {} match ({:.3}%), {} mismatch (Rule C).", c.correct, c.dollar_match, dollar_pct, c.correct - c.dollar_match);

        println!("\n-- missed (C) by constant family --");
        for (k, v) in topn(&missed_family, 20) { println!("  {v:6}  {k}"); }
        println!("\n-- missed (C) by enclosing call --");
        for (k, v) in topn(&missed_func, 20) { println!("  {v:6}  {k}"); }
        println!("\n-- sentinel (A) family swaps (ref->our) --");
        for (k, v) in topn(&sentinel_pair, 20) { println!("  {v:6}  {k}"); }
        println!("\n-- sentinel (A) by enclosing call --");
        for (k, v) in topn(&sentinel_func, 15) { println!("  {v:6}  {k}"); }
        println!("\n-- wrong (B) by enclosing call --");
        for (k, v) in topn(&wrong_func, 20) { println!("  {v:6}  {k}"); }
        println!("\n-- over-application by enclosing call --");
        for (k, v) in topn(&over_func, 20) { println!("  {v:6}  {k}"); }
        println!("=============================================================\n");
    }
}
