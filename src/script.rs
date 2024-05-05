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
    SendFuncSelect,    // select the type of the next argument to SendFunc
    SendFuncCharacter, // either a character ID or null depending on the first arg
}

impl EnumType {
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
        "SetAICharMove" => vec![EnumType::Character],
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
        "SendFunc" => vec![EnumType::Any, EnumType::SendFuncCharacter],
        "SendFunc2" => vec![EnumType::Any, EnumType::SendFuncCharacter],
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
        "SetCharShowList" => vec![EnumType::Character, EnumType::Repeat],
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

pub fn parse_config<T: AsRef<str>>(script: T) -> Result<HashMap<(EnumType, i32), String>> {
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

    Ok(map)
}

fn iter_signature(sig: &[EnumType]) -> impl Iterator<Item = EnumType> + '_ {
    let (slice, repeat_type) = if *sig.last().unwrap() == EnumType::Repeat {
        (&sig[..sig.len() - 1], sig[sig.len() - 2])
    } else {
        (sig, EnumType::Any)
    };
    slice.iter().copied().chain(std::iter::repeat(repeat_type))
}

fn process_expression(expr: &mut Expression, config: &HashMap<(EnumType, i32), String>) -> bool {
    let mut made_changes = false;

    let is_global = matches!(expr, Expression::Global(_));
    let expr = expr.unwrap_global_mut();

    // first, process any function definitions that occur in this expression
    for inner_block in expr.inner_blocks_mut() {
        made_changes = process_block(inner_block, config) || made_changes;
    }

    // walk the AST to explore any sub-expressions
    expr.walk_mut(&mut |e| {
        made_changes = process_expression(e, config) || made_changes;
    });

    if !is_global {
        // we're currently only interested in calls to global functions
        return made_changes;
    }

    let Expression::FunctionCall(name, args) = expr else {
        return made_changes;
    };

    let Some(signature) = SIGNATURES.get(name.as_str()) else {
        return made_changes;
    };

    let mut send_func_select = 0;
    for (arg_expr, arg_type) in args.iter_mut().zip(iter_signature(signature)) {
        let &Expression::Int(arg_value) = arg_expr.unwrap_global() else {
            continue;
        };

        let actual_type = match arg_type {
            EnumType::Any => continue,
            EnumType::Repeat => unreachable!(),
            EnumType::SendFuncSelect => {
                send_func_select = arg_value;
                continue;
            }
            EnumType::SendFuncCharacter => {
                if send_func_select == 1 {
                    EnumType::Null
                } else {
                    EnumType::Character
                }
            }
            _ => arg_type,
        };

        let Some(constant) = config
            .get(&(actual_type, arg_value))
            .or_else(|| match arg_value {
                -1 => config.get(&(EnumType::Initialize, -1)),
                _ => None,
            })
        else {
            println!(
                "Warning: unexpected argument value {} in call to {}",
                arg_value, name
            );
            continue;
        };

        // if we found a match for a symbolic constant, replace the literal expression with one
        // referencing the constant
        *arg_expr = Expression::Global(Box::new(Expression::Variable(Variable(
            constant.clone(),
            None,
        ))));
        made_changes = true;
    }

    made_changes
}

fn process_block(block: &mut Block, config: &HashMap<(EnumType, i32), String>) -> bool {
    let mut made_changes = false;
    for stmt in block.iter_mut() {
        match stmt {
            Statement::ObjectInitialization(expr, init_block) => {
                made_changes = process_expression(expr, config) || made_changes;
                made_changes = process_block(init_block, config) || made_changes;
            }
            Statement::Conditional(conditional, else_block) => {
                let mut condition = Some(conditional);
                while let Some(Conditional(expr, condition_block, next_condition)) = condition {
                    made_changes = process_expression(expr, config) || made_changes;
                    made_changes = process_block(condition_block, config) || made_changes;
                    condition = next_condition.as_deref_mut();
                }
                if let Some(else_block) = else_block {
                    made_changes = process_block(else_block, config) || made_changes;
                }
            }
            Statement::Expression(expr) => {
                made_changes = process_expression(expr, config) || made_changes;
            }
            _ => (),
        }
    }

    made_changes
}

pub fn parse_format_script<T: AsRef<str>>(
    script: T,
    tab_width: Option<usize>,
    config: Option<HashMap<(EnumType, i32), String>>,
) -> Result<String> {
    let mut block = parser::parse(script)?;
    if let Some(constants) = config {
        if process_block(&mut block, &constants) {
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
