use std::collections::HashMap;
use std::str::FromStr;

use anyhow::Result;
use common_macros::hash_map;
use lazy_static::lazy_static;
use strum::{EnumIter, EnumString};

mod parser;
use parser::{Block, Conditional, Expression, Statement, Variable};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, EnumString, EnumIter)]
pub enum EnumType {
    #[strum(serialize = "MTAS")]
    Animation,
    #[strum(serialize = "CHID")]
    Character,
    #[strum(serialize = "SAY")]
    Say,
    #[strum(serialize = "COMMAND")]
    Command,
    #[strum(serialize = "PARAM_ATTACK")]
    ParamAttack,
    #[strum(serialize = "PARAM_WEAPON")]
    ParamWeapon,
    #[strum(serialize = "PARAM_KICK")]
    ParamKick,
    #[strum(serialize = "FEEL")]
    Feeling,
    #[strum(serialize = "EVENT")]
    Event,
    #[strum(serialize = "EFFECT")]
    Effect,
    #[strum(serialize = "CAMERA")]
    Camera,
    #[strum(serialize = "WATCH")]
    Watch,
    #[strum(serialize = "MAPID")]
    Map,
    #[strum(serialize = "TIME")]
    Time,
    #[strum(serialize = "DAMAGE")]
    Damage,
    #[strum(serialize = "AI")]
    Ai,
    #[strum(serialize = "OBJ")]
    Object,
    #[strum(serialize = "BGM")]
    Bgm,
    #[strum(serialize = "FRIEND")]
    Friend,
    #[strum(serialize = "EVENTPRO")]
    EventProgress,
    #[strum(serialize = "FOOTING")]
    Footing,
    #[strum(serialize = "BTN")]
    Button,
    #[strum(serialize = "OBJECT")]
    ObjectSet,
    // these don't follow the normal naming convention and need special handling
    Boolean,
    Relation,
    FadeDir,
    FadeType,
    Initialize,
    Null,
    Any,               // any other type not identified above
    Repeat,            // repeat the previous type (for vararg functions)
    Select,            // select the type of a following argument
    SendFuncCharacter, // either a character ID or null depending on the previous select arg
}

impl EnumType {
    fn is_concrete(&self) -> bool {
        !matches!(
            self,
            EnumType::Any | EnumType::Repeat | EnumType::Select | EnumType::SendFuncCharacter
        )
    }

    fn get_constant_type(constant: &str) -> Option<Self> {
        match constant {
            "ON" | "OFF" => Some(Self::Boolean),
            "NO_RELATION" | "ENEMY_RELATION" | "FRIEND_RELATION" => Some(Self::Relation),
            "INIT" => Some(Self::Initialize),
            "NULL" => Some(Self::Null),
            "FADE_IN_INIT" | "FADE_IN" | "FADE_OUT" => Some(Self::FadeDir),
            "FADE_NORMAL" | "FADE_SPECIAL" => Some(Self::FadeType),
            "SAY_WEAPON_ON" | "SAY_WEAPON_OFF" => Some(Self::Command),
            _ => {
                let index = constant
                    .match_indices('_')
                    .find(|(_, s)| *s != "PARAM")? // PARAMs need the next part of the name as well
                    .0;
                let prefix = &constant[..index];
                Self::from_str(prefix).ok()
            }
        }
    }
}

lazy_static! {
    static ref SIGNATURES: HashMap<&'static str, Vec<EnumType>> = hash_map! {
        "DelAIChar" => vec![EnumType::Character],
        "SetAIChar" => vec![EnumType::Character, EnumType::Ai],
        "GetAIChar" => vec![EnumType::Character],
        "SetAITargetItem" => vec![EnumType::Character, EnumType::Object],
        "SetCharPos" => vec![EnumType::Character],
        "SetCharDir" => vec![EnumType::Character, EnumType::Character],
        "SetCharDir2" => vec![EnumType::Character],
        "SetAIBackLimit" => vec![EnumType::Character],
        "SetAIWalkLimit" => vec![EnumType::Character],
        "SetAISiegeLimit" => vec![EnumType::Character],
        "SetAIRunLimit" => vec![EnumType::Character],
        "SetSoloCamera" => vec![EnumType::Character],
        "SetFixCamera" => vec![EnumType::Character],
        "Say" => vec![EnumType::Character, EnumType::Character, EnumType::Any, EnumType::Any, EnumType::Any, EnumType::Say],
        "SetSayMotion" => vec![EnumType::Character, EnumType::Command],
        "SetTalkSelect" => vec![EnumType::Character],
        "SetTimeAction" => vec![EnumType::Character, EnumType::Character],
        "SetCharAction" => vec![EnumType::Character, EnumType::Command],
        "SetAICharMove" => vec![EnumType::Character, EnumType::Command],
        "SetEventMode" => vec![EnumType::Character, EnumType::Event, EnumType::Repeat],
        "SubEventMode" => vec![EnumType::Character, EnumType::Event, EnumType::Repeat],
        "GetCharPos" => vec![EnumType::Character],
        "SetCharDraw" => vec![EnumType::Character, EnumType::Boolean],
        "AddSamuraiValue" => vec![EnumType::Character],
        "SubSamuraiValue" => vec![EnumType::Character],
        "SetLineAction" => vec![EnumType::Character],
        "SetMapID" => vec![EnumType::Map],
        "SetCharLevel" => vec![EnumType::Character],
        "SetEventUseCharList" => vec![EnumType::Character, EnumType::Repeat],
        "SetCharDrawOnList" => vec![EnumType::Character, EnumType::Repeat],
        "SetCharDrawOffList" => vec![EnumType::Character, EnumType::Repeat],
        "SetAddCharScript" => vec![EnumType::Character],
        "SetCharNoCollMode" => vec![EnumType::Character, EnumType::Boolean],
        "SetAIGroupRelation" => vec![EnumType::Footing, EnumType::Footing, EnumType::Relation],
        "SendFunc" => vec![EnumType::Select, EnumType::SendFuncCharacter],
        "SendFunc2" => vec![EnumType::Select, EnumType::SendFuncCharacter],
        "SetAddCharScriptList" => vec![EnumType::Any, EnumType::Character, EnumType::Repeat],
        "SetCharNeckAction" => vec![EnumType::Character],
        "SetCharFace" => vec![EnumType::Character, EnumType::Animation],
        "SetObjDraw" => vec![EnumType::Object, EnumType::Boolean],
        "SetCharGroupID" => vec![EnumType::Character, EnumType::Footing],
        "SetCharLife" => vec![EnumType::Character],
        "SetCharHiFaceMode" => vec![EnumType::Character, EnumType::Boolean],
        "SetPosLineAction" => vec![EnumType::Character],
        "SetAIAllStop" => vec![EnumType::Boolean],
        "SetCharForm" => vec![EnumType::Character],
        "SetCutCamera" => vec![EnumType::Camera],
        "SetCharFriendFlag" => vec![EnumType::Character, EnumType::Friend],
        "SetCameraPos" => vec![EnumType::Camera],
        "SetSayPos" => vec![EnumType::Character],
        "SetCharMove" => vec![EnumType::Character, EnumType::Command],
        "SetCharShowList" => vec![EnumType::Boolean, EnumType::Character, EnumType::Repeat],
        "SetCharTarget" => vec![EnumType::Character, EnumType::Character],
        "GetCharDead" => vec![EnumType::Character],
        "SetMapTimeID" => vec![EnumType::Time],
        "SetCharWatch" => vec![EnumType::Character],
        "SetCharPosFixMode" => vec![EnumType::Character, EnumType::Boolean],
        "SetObjMoveTetudo" => vec![EnumType::Boolean],
        "SetCharNoDamageMode" => vec![EnumType::Character, EnumType::Boolean],
        "ScreenEffect" => vec![EnumType::Effect, EnumType::FadeDir, EnumType::FadeType],
        "SetEventProFlag" => vec![EnumType::Any, EnumType::EventProgress],
        "VoicePlay" => vec![EnumType::Any, EnumType::Any, EnumType::Character],
        "StartCharTrace" => vec![EnumType::Character, EnumType::Character, EnumType::Command],
        "SetPadMode" => vec![EnumType::Boolean],
        "SetObjAction" => vec![EnumType::Object],
        "GetCharThrowCount" => vec![EnumType::Character],
        "GetCharStatus" => vec![EnumType::Character, EnumType::Event],
        "AddCharDaikonFlag" => vec![EnumType::Character],
        "SubCharDaikonFlag" => vec![EnumType::Character],
        "GetObjChar" => vec![EnumType::Character],
        "ClearFrontEvent" => vec![EnumType::Character],
        "GetDamageKind" => vec![EnumType::Character],
        "AddEventMode" => vec![EnumType::Character, EnumType::Event, EnumType::Repeat],
        "SetCharWaiting" => vec![EnumType::Character],
        "SetCharDeathBlow" => vec![EnumType::Character],
        "StopCharTrace" => vec![EnumType::Character],
        "GetCharFriendFlag" => vec![EnumType::Character],
        "GetCharRange" => vec![EnumType::Character],
        // callback functions
        "MapIn" => vec![EnumType::Map],
        "MapOut" => vec![EnumType::Map],
        "Collision" => vec![EnumType::Character, EnumType::Character],
        "Damage" => vec![EnumType::Character, EnumType::Character],
        "TalkEnd" => vec![EnumType::Character, EnumType::Character],
        "TalkSelect" => vec![EnumType::Character],
        "PosJoin" => vec![EnumType::Character],
        "PosLeave" => vec![EnumType::Character],
        "Join" => vec![EnumType::Character, EnumType::Character],
        "Leave" => vec![EnumType::Character, EnumType::Character],
        "TimeOut" => vec![EnumType::Character, EnumType::Character],
        "SayDead" => vec![EnumType::Character, EnumType::Character],
        "NpcOut" => vec![EnumType::Character],
        "WeaponOn" => vec![EnumType::Character, EnumType::Character],
        "WeaponOff" => vec![EnumType::Character, EnumType::Character],
        "Dead" => vec![EnumType::Character, EnumType::Character],
        "Watch" => vec![EnumType::Character, EnumType::Character],
    };
}

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
    scope: Vec<HashMap<String, EnumType>>,
    made_changes: bool,
}

impl ScriptFormatter {
    pub fn new() -> Self {
        Self {
            config: None,
            scope: vec![],
            made_changes: false,
        }
    }

    fn iter_signature(sig: &[EnumType]) -> impl Iterator<Item = EnumType> + '_ {
        let (slice, repeat_type) = if *sig.last().unwrap() == EnumType::Repeat {
            (&sig[..sig.len() - 1], sig[sig.len() - 2])
        } else {
            (sig, EnumType::Any)
        };
        slice.iter().copied().chain(std::iter::repeat(repeat_type))
    }

    fn scope_lookup<'a, 'b, T: Iterator<Item = &'a HashMap<String, EnumType>>>(
        name: &'b String,
        mut it: T,
    ) -> Option<EnumType> {
        it.find_map(|m| m.get(name)).copied()
    }

    fn reset(&mut self) {
        self.scope.clear();
        self.made_changes = false;
    }

    fn get_var_type(&self, name: &String, is_global: bool) -> Option<EnumType> {
        if is_global {
            Self::scope_lookup(name, self.scope.iter().rev())
        } else {
            Self::scope_lookup(name, self.scope.iter())
        }
    }

    fn get_constant(&self, value_type: EnumType, value: i32) -> Option<Expression> {
        if !value_type.is_concrete() {
            return None;
        }

        let config = self.config.as_ref().unwrap();
        config
            .get(&(value_type, value))
            .or_else(|| match value {
                -1 => config.get(&(EnumType::Initialize, -1)),
                _ => None,
            })
            .map(|s| Expression::new_global_var(s.clone()))
    }

    fn get_var_constant(&self, name: &String, value: i32, is_global: bool) -> Option<Expression> {
        self.get_constant(self.get_var_type(name, is_global)?, value)
    }

    fn process_call(&mut self, name: &String, args: &mut Vec<Expression>) {
        let Some(signature) = SIGNATURES.get(name.as_str()) else {
            return;
        };

        let mut select = 0;
        for (arg_expr, arg_type) in args.iter_mut().zip(Self::iter_signature(signature)) {
            let &Expression::Int(arg_value) = arg_expr.unwrap_global().0 else {
                continue;
            };

            let actual_type = match arg_type {
                EnumType::Any => continue,
                EnumType::Repeat => unreachable!(),
                EnumType::Select => {
                    select = arg_value;
                    continue;
                }
                EnumType::SendFuncCharacter => {
                    if select == 1 {
                        EnumType::Null
                    } else {
                        EnumType::Character
                    }
                }
                _ => arg_type,
            };

            match self.get_constant(actual_type, arg_value) {
                Some(constant) => {
                    // if we found a match for a symbolic constant, replace the literal expression with one
                    // referencing the constant
                    *arg_expr = constant;
                    self.made_changes = true;
                }
                None => {
                    println!(
                        "Warning: unexpected argument value {} in call to {}",
                        arg_value, name
                    );
                }
            }
        }
    }

    fn push_scope<T: Iterator<Item = EnumType>>(&mut self, args: &[String], types: T) {
        let mut new_scope = HashMap::with_capacity(args.len());
        for (arg, arg_type) in args.iter().zip(types) {
            new_scope.insert(arg.clone(), arg_type);
        }
        self.scope.push(new_scope);
    }

    fn push_dummy_scope(&mut self, args: &[String]) {
        self.push_scope(args, std::iter::repeat(EnumType::Any));
    }

    fn check_for_comparison(
        &mut self,
        var: &mut Expression,
        method: &str,
        args: &mut Vec<Expression>,
    ) {
        // attributes not currently supported
        if let (Expression::Variable(Variable(var_name, None)), is_global_object) =
            var.unwrap_global()
        {
            // if this is a comparison or assignment method with a single integer argument
            if args.len() == 1
                && matches!(method, "eq" | "lt" | "le" | "gt" | "ge" | "<" | ">" | "=")
            {
                if let &Expression::Int(arg_value) = args[0].unwrap_global().0 {
                    // try to look up the variable in the scope
                    if let Some(constant) =
                        self.get_var_constant(var_name, arg_value, is_global_object)
                    {
                        // replace the literal with the constant
                        args[0] = constant;
                        self.made_changes = true;
                    }
                }
            }
        }
    }

    fn process_expression(&mut self, expr: &mut Expression) {
        let (expr, is_global) = expr.unwrap_global_mut();

        // do expression-type-specific processing
        match expr {
            Expression::MethodCall(var, method, args) => {
                self.check_for_comparison(var, method, args)
            }
            Expression::FunctionCall(name, args) if is_global => self.process_call(name, args),
            _ => (),
        }

        // continue down the AST

        // if this is defining a function for a well-known callback, propagate type information
        let mut pushed_scope = false;
        if let Some((lhs, Expression::FunctionDefinition(args, _))) = expr.declaration() {
            // well-known callbacks are always globals
            if is_global || matches!(lhs, Expression::Global(_)) {
                // attribute types not currently supported
                if let Expression::Variable(Variable(name, None)) = lhs.unwrap_global().0 {
                    if let Some(signature) = SIGNATURES.get(name.as_str()) {
                        // add types
                        self.push_scope(args, Self::iter_signature(signature));
                        pushed_scope = true;
                    }
                }
            }
        }

        // process any function definitions that occur in this expression
        for (inner_args, inner_block) in expr.inner_blocks_mut() {
            // if we didn't find the actual types above, create a dummy scope so we don't look things up
            // in the wrong scope by accident
            if !pushed_scope {
                self.push_dummy_scope(inner_args);
            }

            self.process_block(inner_block);

            // pop the dummy scope if we added one
            if !pushed_scope {
                self.scope.pop();
            }
        }

        if pushed_scope {
            self.scope.pop();
        }

        // walk the AST to explore any sub-expressions
        expr.walk_mut(&mut |e| {
            self.process_expression(e);
        });
    }

    fn process_block(&mut self, block: &mut Block) {
        for stmt in block.iter_mut() {
            match stmt {
                Statement::ObjectInitialization(expr, init_block) => {
                    self.process_expression(expr);
                    self.process_block(init_block);
                }
                Statement::Conditional(conditional, else_block) => {
                    let mut condition = Some(conditional);
                    while let Some(Conditional(expr, condition_block, next_condition)) = condition {
                        self.process_expression(expr);
                        self.process_block(condition_block);
                        condition = next_condition.as_deref_mut();
                    }
                    if let Some(else_block) = else_block {
                        self.process_block(else_block);
                    }
                }
                Statement::Expression(expr) => {
                    self.process_expression(expr);
                }
                _ => (),
            }
        }
    }

    pub fn use_config<T: AsRef<str>>(&mut self, script: T) -> Result<()> {
        let parsed = parser::parse(script)?;
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

        let mut block = parser::parse(script)?;
        if self.config.is_some() {
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
