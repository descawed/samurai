use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, anyhow, bail};

mod analysis;
mod parse;
mod types;

use analysis::Analyzer;
use parse::{Block, Conditional, Expression, Statement};
use types::{EnumType, ScriptValue, SharedScope, SharedSignature, Variable, obfuscate};

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
    made_changes: bool,
    quiet: bool,
    obfuscate: bool,
    include_dir: Option<PathBuf>,
}

impl ScriptFormatter {
    pub fn new() -> Self {
        Self {
            config: None,
            made_changes: false,
            quiet: false,
            obfuscate: false,
            include_dir: None,
        }
    }

    pub fn set_quiet(&mut self, quiet: bool) {
        self.quiet = quiet;
    }

    pub fn set_obfuscate(&mut self, obfuscate: bool) {
        self.obfuscate = obfuscate;
    }

    pub fn set_include_dir(&mut self, include_dir: Option<PathBuf>) {
        self.include_dir = include_dir;
    }

    fn reset(&mut self) {
        self.made_changes = false;
    }

    fn get_constant(&self, value_type: EnumType, value: i32) -> Option<Expression> {
        if !value_type.is_concrete() {
            return None;
        }

        let config = self.config.as_ref()?;
        config
            .get(&(value_type, value))
            .or_else(|| match value {
                -1 => config.get(&(EnumType::Initialize, -1)),
                0 => config.get(&(EnumType::Null, 0)),
                _ => None,
            })
            .map(|s| Expression::new_var(s.clone()))
    }

    fn use_constant(&mut self, value_type: EnumType, expr: &mut Expression, select: Option<i32>) {
        let actual_type = value_type.select_type(select);
        if !actual_type.is_concrete() {
            return;
        }

        let &Expression::Int(value) = expr.unwrap_global().0 else {
            return;
        };

        match self.get_constant(actual_type, value) {
            Some(constant) => {
                // if we found a match for a symbolic constant, replace the literal expression with one
                // referencing the constant
                *expr = constant;
                self.made_changes = true;
            }
            None => {
                if !self.quiet {
                    println!(
                        "Warning: unexpected value {} for type {:?}",
                        value, actual_type,
                    );
                }
            }
        }
    }

    fn process_call(&mut self, args: &mut [Expression], signature: &SharedSignature) {
        let mut select = None;
        for (arg_expr, arg_type) in args.iter_mut().zip(signature.borrow().iter()) {
            if let (&Expression::Int(arg_value), EnumType::Select) =
                (arg_expr.unwrap_global().0, arg_type)
            {
                select = Some(arg_value);
            }

            self.use_constant(arg_type, arg_expr, select);
        }
    }

    fn process_method(&mut self, object: &ScriptValue, method: &str, args: &mut [Expression]) {
        match (args.len(), method, object) {
            // if this is a comparison or assignment to a scalar with a single argument
            (1, "eq" | "lt" | "le" | "gt" | "ge" | "<" | ">" | "=", _) => {
                self.use_constant(object.get_type(), &mut args[0], None);
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
                if let (Expression::Variable(var), is_global_obj) = var.unwrap_global()
                    && let Some(obj) = scope.borrow().lookup(var, is_global || is_global_obj)
                {
                    self.process_method(&obj, method, args);
                }
            }
            Expression::FunctionCall(name, args) => {
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
                    self.use_constant(obj.get_type(), rhs, None);
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
                    self.process_expression(expr, &scope);
                    self.process_block(init_block);
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
        let declarations = parsed.into_iter().filter_map(|s| match s {
            Statement::Expression(e) => e.into_declaration(),
            _ => None,
        });
        for (name_expr, value_expr) in declarations {
            let Expression::Variable(Variable(name, None)) = name_expr else {
                continue;
            };

            let Expression::Int(value) = value_expr else {
                continue;
            };

            let Some(constant_type) = EnumType::get_constant_type(&name) else {
                continue;
            };

            map.insert((constant_type, value), name);
        }

        self.config = Some(map);
        Ok(())
    }

    pub fn format_script<T: AsRef<str>>(
        &mut self,
        script: T,
        tab_width: Option<usize>,
    ) -> Result<String> {
        self.reset();

        let mut block = parse::parse(script)?;
        if self.config.is_some() {
            let mut analyzer = Analyzer::new();
            analyzer.infer_types(&mut block, self.config.as_ref());
            self.process_block(&mut block);
        }
        let text = block.to_string_top_level();
        Ok(match tab_width {
            Some(num_spaces) => text.replace('\t', " ".repeat(num_spaces).as_str()),
            None => text,
        })
    }

    /// Replace symbolic constants with their literal values and function names with their
    /// obfuscated equivalents in an expression
    ///
    /// `allow_constants` should be false when the expression names a variable being declared or
    /// initialized, as such a variable is not a constant reference even if it shares a name with
    /// a constant.
    fn unformat_expression(
        &self,
        expr: &mut Expression,
        constants: &HashMap<&str, i32>,
        allow_constants: bool,
    ) {
        // replace references to config constants with their literal values
        if allow_constants
            && let (Expression::Variable(Variable(name, None)), _) = expr.unwrap_global()
            && let Some(&value) = constants.get(name.as_str())
        {
            *expr = Expression::Int(value);
            return;
        }

        let (expr, _) = expr.unwrap_global_mut();
        match expr {
            Expression::ReferenceDeclaration(lhs, rhs) | Expression::ValueDeclaration(lhs, rhs) => {
                if self.obfuscate
                    && matches!(rhs.as_ref(), Expression::FunctionDefinition(_, _))
                    && let (Expression::Variable(Variable(name, None)), _) =
                        lhs.unwrap_global_mut()
                {
                    // this may be a global event callback declaration; attempt to obfuscate
                    obfuscate(name);
                }

                self.unformat_expression(lhs, constants, false);
                self.unformat_expression(rhs, constants, true);
            }
            Expression::FunctionCall(name, args) => {
                if self.obfuscate {
                    obfuscate(name);
                }
                for arg in args {
                    self.unformat_expression(arg, constants, true);
                }
            }
            Expression::MethodCall(object, _, args) => {
                self.unformat_expression(object, constants, true);
                for arg in args {
                    self.unformat_expression(arg, constants, true);
                }
            }
            Expression::TernaryConditional(condition, true_expr, false_expr) => {
                self.unformat_expression(condition, constants, true);
                self.unformat_expression(true_expr, constants, true);
                self.unformat_expression(false_expr, constants, true);
            }
            Expression::FunctionDefinition(_, block) => {
                self.unformat_block(block, constants);
            }
            _ => (),
        }
    }

    /// Replace symbolic constants with their literal values and function names with their
    /// obfuscated equivalents in a block
    fn unformat_block(&self, block: &mut Block, constants: &HashMap<&str, i32>) {
        for stmt in block.iter_mut() {
            match stmt {
                Statement::ObjectInitialization(expr, init_block) => {
                    self.unformat_expression(expr, constants, false);
                    self.unformat_block(init_block, constants);
                }
                Statement::WhileLoop(expr, loop_block) => {
                    self.unformat_expression(expr, constants, true);
                    self.unformat_block(loop_block, constants);
                }
                Statement::Conditional(conditional, else_block) => {
                    let mut condition = Some(conditional);
                    while let Some(Conditional(expr, condition_block, next_condition)) = condition {
                        self.unformat_expression(expr, constants, true);
                        self.unformat_block(condition_block, constants);
                        condition = next_condition.as_deref_mut();
                    }
                    if let Some(else_block) = else_block {
                        self.unformat_block(else_block, constants);
                    }
                }
                Statement::Expression(expr) => {
                    self.unformat_expression(expr, constants, true);
                }
                _ => (),
            }
        }
    }

    /// If the statement is an include directive (`$Include "filename";`), get the included filename
    fn include_filename(stmt: &Statement) -> Option<&str> {
        let Statement::Expression(expr) = stmt else {
            return None;
        };

        let (Expression::FunctionCall(name, args), _) = expr.unwrap_global() else {
            return None;
        };

        if name != "Include" {
            return None;
        }

        match args.as_slice() {
            [Expression::String(filename)] => Some(filename),
            _ => None,
        }
    }

    /// Search `dir` for a file whose name matches `filename` case-insensitively
    fn resolve_include(dir: &Path, filename: &str) -> Result<PathBuf> {
        // fast path: the name matches exactly
        let exact = dir.join(filename);
        if exact.is_file() {
            return Ok(exact);
        }

        for entry in
            fs::read_dir(dir).with_context(|| format!("Failed to list {}", dir.display()))?
        {
            let entry = entry?;
            if entry
                .file_name()
                .to_string_lossy()
                .eq_ignore_ascii_case(filename)
                && entry.path().is_file()
            {
                return Ok(entry.path());
            }
        }

        Err(anyhow!(
            "Include file {:?} not found in {}",
            filename,
            dir.display()
        ))
    }

    /// Inline includes in any function definitions contained in an expression
    fn inline_includes_in_expression(
        expr: &mut Expression,
        dir: &Path,
        stack: &mut Vec<String>,
    ) -> Result<()> {
        for (_, inner_block) in expr.inner_blocks_mut() {
            Self::inline_includes(inner_block, dir, stack)?;
        }
        Ok(())
    }

    /// Replace include directives with the parsed contents of the included files
    ///
    /// `stack` tracks the chain of files currently being included so circular includes can be
    /// detected.
    fn inline_includes(block: &mut Block, dir: &Path, stack: &mut Vec<String>) -> Result<()> {
        let mut i = 0;
        while i < block.len() {
            let Some(filename) = Self::include_filename(&block[i]) else {
                match &mut block[i] {
                    Statement::ObjectInitialization(expr, init_block) => {
                        Self::inline_includes_in_expression(expr, dir, stack)?;
                        Self::inline_includes(init_block, dir, stack)?;
                    }
                    Statement::WhileLoop(expr, loop_block) => {
                        Self::inline_includes_in_expression(expr, dir, stack)?;
                        Self::inline_includes(loop_block, dir, stack)?;
                    }
                    Statement::Conditional(conditional, else_block) => {
                        let mut condition = Some(conditional);
                        while let Some(Conditional(expr, condition_block, next_condition)) =
                            condition
                        {
                            Self::inline_includes_in_expression(expr, dir, stack)?;
                            Self::inline_includes(condition_block, dir, stack)?;
                            condition = next_condition.as_deref_mut();
                        }
                        if let Some(else_block) = else_block {
                            Self::inline_includes(else_block, dir, stack)?;
                        }
                    }
                    Statement::Expression(expr) => {
                        Self::inline_includes_in_expression(expr, dir, stack)?;
                    }
                    _ => (),
                }
                i += 1;
                continue;
            };

            let key = filename.to_lowercase();
            if stack.contains(&key) {
                bail!("Circular include of {:?}", filename);
            }

            let path = Self::resolve_include(dir, filename)?;
            let text = fs::read_to_string(&path)
                .with_context(|| format!("Failed to read include file {}", path.display()))?;
            let mut included = parse::parse(text)
                .with_context(|| format!("Failed to parse include file {}", path.display()))?;

            stack.push(key);
            Self::inline_includes(&mut included, dir, stack)?;
            stack.pop();

            let num_statements = included.len();
            block.splice(i..=i, included);
            // the included statements have already been fully processed, so skip over them
            i += num_statements;
        }

        Ok(())
    }

    pub fn unformat_script<T: AsRef<str>>(&self, script: T) -> Result<String> {
        if self.config.is_none() && !self.obfuscate && self.include_dir.is_none() {
            return Ok(unformat_script(script.as_ref()));
        }

        let mut block = parse::parse(script)?;
        if let Some(dir) = &self.include_dir {
            Self::inline_includes(&mut block, dir, &mut Vec::new())?;
        }
        let constants: HashMap<&str, i32> = self
            .config
            .iter()
            .flatten()
            .map(|(&(_, value), name)| (name.as_str(), value))
            .collect();
        self.unformat_block(&mut block, &constants);

        Ok(unformat_script(block.to_string_top_level().as_str()))
    }
}

impl Default for ScriptFormatter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("samurai_{}_{}", name, std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn test_inline_includes() {
        let dir = test_dir("inline_includes");
        // the include search should be case-insensitive
        fs::write(dir.join("COMMON.H"), "#a | 1;\n$Include \"Nested.h\";").unwrap();
        fs::write(dir.join("nested.h"), "#b : 2;").unwrap();

        let mut formatter = ScriptFormatter::new();
        formatter.set_include_dir(Some(dir.clone()));
        let result = formatter.unformat_script("$Include \"common.h\";\n$Answer 42;");

        fs::remove_dir_all(&dir).unwrap();

        let result = result.unwrap();
        assert!(!result.contains("Include"));
        let a = result.find("#a | 1;").unwrap();
        let b = result.find("#b : 2;").unwrap();
        let answer = result.find("$Answer 42;").unwrap();
        assert!(a < b && b < answer);
    }

    #[test]
    fn test_circular_include() {
        let dir = test_dir("circular_include");
        fs::write(dir.join("a.h"), "$Include \"b.h\";").unwrap();
        fs::write(dir.join("b.h"), "$Include \"A.H\";").unwrap();

        let mut formatter = ScriptFormatter::new();
        formatter.set_include_dir(Some(dir.clone()));
        let result = formatter.unformat_script("$Include \"a.h\";");

        fs::remove_dir_all(&dir).unwrap();

        let error = result.unwrap_err().to_string();
        assert!(error.contains("Circular include"));
    }

    #[test]
    fn test_missing_include() {
        let dir = test_dir("missing_include");

        let mut formatter = ScriptFormatter::new();
        formatter.set_include_dir(Some(dir.clone()));
        let result = formatter.unformat_script("$Include \"nope.h\";");

        fs::remove_dir_all(&dir).unwrap();

        assert!(result.unwrap_err().to_string().contains("not found"));
    }
}
