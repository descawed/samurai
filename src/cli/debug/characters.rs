use std::collections::HashSet;

use ratatui::Frame;
use ratatui::layout::Rect;
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{List, ListItem, ListState};

use crate::debug::*;

use super::{labeled_constant, labeled_constant_hex, panel_block};

/// Style for the indented detail rows shown when a character is expanded.
fn detail_style() -> Style {
    Style::new().fg(Color::DarkGray)
}

/// The always-visible summary row for a character.
fn summary_line(data: &CharacterData) -> Line<'static> {
    let mut spans = vec![
        Span::raw(format!("{:>3} ", data.chara_id.value())),
        Span::raw(format!("{:<17} ", data.chara_id.constant_name().unwrap_or(""))),
        Span::raw(format!("{:<22}", data.chara_id.display_name())),
        Span::raw(format!(" {}/{}", data.health, data.max_health)),
    ];
    if data.is_dead() {
        spans.push(Span::styled(" [dead]", Style::new().fg(Color::Red)));
    }
    Line::from(spans)
}

/// One detail row, e.g. `  Footing: 4 (FOOTING_NORMAL)`.
fn detail(label: &str, value: String) -> Line<'static> {
    Line::from(format!("    {label}: {value}")).style(detail_style())
}

/// Noteworthy flags enabled for a character
fn describe_character_flags(chara: &Character) -> String {
    let mut labels = Vec::with_capacity(6);

    if chara.is_invincible() {
        labels.push("invincible");
    }

    if chara.is_pos_fix_mode() {
        labels.push("pos fix mode");
    }

    if chara.is_stopped() {
        labels.push("stop");
    }

    if chara.is_dead() {
        labels.push("dead");
    }

    if chara.is_hi_face_mode() {
        labels.push("hi face mode");
    }

    if chara.say_dead_flag() {
        labels.push("say dead");
    }

    if !labels.is_empty() {
        labels.join(", ")
    } else {
        "none".to_string()
    }
}

/// Describe watch type and watched object for WATCH_OBJECT type
fn describe_watch_type(chara: &Character) -> String {
    let mut watch_type = chara.watch_type.display_name().to_string();
    if chara.watch_type.value() == 2 /* WATCH_OBJECT */ {
        watch_type.push_str(" (");
        if chara.is_drop_watch() {
            watch_type.push_str("drop");
        } else {
            watch_type.push_str(chara.watched_obj_id.display_name());
        }
        watch_type.push(')');
    }

    watch_type
}

fn detail_lines(address: u32, chara: &Character, data: &CharacterData) -> Vec<Line<'static>> {
    let position = chara.position;
    let active_events: Vec<&str> = chara
        .event_mode_flags()
        .into_iter()
        .filter_map(|(name, set)| set.then_some(name))
        .collect();
    let events = if active_events.is_empty() {
        "none".to_string()
    } else {
        active_events.join(", ")
    };
    let event_line = format!("{:08X} ({})", chara.event_modes, events);

    vec![
        detail("Address", format!("{address:08X}")),
        detail("Type ID", data.chara_type_id.to_string()),
        detail("Level", data.level.to_string()),
        detail(
            "Footing",
            labeled_constant(data.footing.value(), data.footing.constant_name()),
        ),
        detail(
            "Friend",
            format!("{} ({})", data.friend_flag.value(), data.friend_flag.display_name()),
        ),
        detail("Daikon", data.daikon_flag.to_string()),
        detail(
            "Weapon",
            format!(
                "id {} (equipped {}/{})",
                data.weapon_id, chara.equipped_weapon_index, chara.num_weapons
            ),
        ),
        detail(
            "AI",
            format!(
                "{}  group {}",
                labeled_constant_hex(chara.ai_mode.value(), chara.ai_mode.constant_name()),
                chara.ai_group_id
            ),
        ),
        detail(
            "Animation",
            labeled_constant_hex(chara.animation_id.value(), chara.animation_id.constant_name()),
        ),
        detail(
            "Command",
            format!(
                "cur {} last {} AI {}",
                labeled_constant(chara.current_command_id.value(), chara.current_command_id.constant_name()),
                labeled_constant(chara.last_command_id.value(), chara.last_command_id.constant_name()),
                labeled_constant(chara.ai_command.value(), chara.ai_command.constant_name()),
            ),
        ),
        detail(
            "Watch",
            if chara.is_watch_enabled() {
                format!(
                    "{} -> {}",
                    describe_watch_type(chara),
                    labeled_constant(chara.watched_chara_id.value(), chara.watched_chara_id.constant_name()),
                )
            } else {
                "none".to_string()
            },
        ),
        detail(
            "Pos",
            format!("{:.1}, {:.1}, {:.1}", position[0], position[1], position[2]),
        ),
        detail(
            "Special",
            format!("{}  throws {}", chara.special_state, chara.throw_count),
        ),
        detail("Events", event_line),
        detail("Flags", describe_character_flags(chara)),
    ]
}

fn build_item(address: u32, chara: &Character, data: &CharacterData, expanded: bool) -> ListItem<'static> {
    let mut lines = vec![summary_line(data)];
    if expanded {
        lines.extend(detail_lines(address, chara, data));
    }
    ListItem::new(lines)
}

pub fn render(
    frame: &mut Frame,
    area: Rect,
    game: &Game,
    state: &mut ListState,
    expanded: &HashSet<usize>,
    focused: bool,
) {
    let items: Vec<ListItem> = game
        .iter_characters()
        .enumerate()
        .map(|(i, (address, chara, data))| build_item(address, chara, data, expanded.contains(&i)))
        .collect();

    let title = format!("Characters ({})", items.len());
    let list = List::new(items)
        .block(panel_block(title, focused))
        .highlight_symbol("> ")
        .highlight_style(Style::new().add_modifier(Modifier::BOLD));
    frame.render_stateful_widget(list, area, state);
}
