use std::collections::HashMap;
use std::str::FromStr;

use anyhow::Result;
use strum::{EnumIter, EnumString};

mod parser;
use parser::{Expression, Statement, Variable};

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
    #[strum(serialize = "FADE")]
    Fade,
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
    // these two don't follow the normal naming convention and need special handling
    Boolean,
    Relation,
}

impl EnumType {
    fn get_constant_type(constant: &str) -> Option<Self> {
        match constant {
            "ON" | "OFF" => Some(Self::Boolean),
            "NO_RELATION" | "ENEMY_RELATION" | "FRIEND_RELATION" => Some(Self::Relation),
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

pub fn parse_format_script<T: AsRef<str>>(
    script: T,
    tab_width: Option<usize>,
    config: Option<HashMap<(EnumType, i32), String>>,
) -> Result<String> {
    let mut block = parser::parse(script)?;
    if let Some(constants) = config {}
    let text = block.to_string_top_level();
    Ok(match tab_width {
        Some(num_spaces) => text.replace('\t', " ".repeat(num_spaces).as_str()),
        None => text,
    })
}
