use std::collections::HashMap;

use anyhow::Result;

mod analysis;
mod parse;
mod types;

use analysis::Analyzer;
use parse::{Block, Conditional, Expression, Statement};
use types::{EnumType, ScriptValue, SharedScope, SharedSignature, Variable};

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
}

impl ScriptFormatter {
    pub fn new() -> Self {
        Self {
            config: None,
            made_changes: false,
        }
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
                _ => None,
            })
            .map(|s| Expression::new_global_var(s.clone()))
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
                println!(
                    "Warning: unexpected value {} for type {:?}",
                    value, actual_type,
                );
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
                if let (Expression::Variable(var), is_global_obj) = var.unwrap_global() {
                    if let Some(obj) = scope.borrow().lookup(var, is_global || is_global_obj) {
                        self.process_method(&obj, method, args);
                    }
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
                if let (Expression::Variable(ref var), is_global_var) = lhs.unwrap_global() {
                    if let Some(obj) = scope.borrow().lookup(var, is_global || is_global_var) {
                        self.use_constant(obj.get_type(), rhs, None);
                    }
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
            if self.made_changes {
                // if we actually made changes, insert an include of config.h at the beginning of the script
                block.insert(
                    0,
                    Statement::Expression(Expression::Global(Box::new(Expression::FunctionCall(
                        String::from("Include"),
                        vec![Expression::String(String::from("config.h"))],
                    )))),
                );
            }
        }
        let text = block.to_string_top_level();
        Ok(match tab_width {
            Some(num_spaces) => text.replace('\t', " ".repeat(num_spaces).as_str()),
            None => text,
        })
    }
}

impl Default for ScriptFormatter {
    fn default() -> Self {
        Self::new()
    }
}
