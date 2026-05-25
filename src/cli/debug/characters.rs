use std::collections::HashSet;

use ratatui::Frame;
use ratatui::layout::Rect;
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{List, ListItem, ListState};

use crate::debug::*;

use super::{labeled_constant, panel_block};

/// Style for the indented detail rows shown when a character is expanded.
fn detail_style() -> Style {
    Style::new().fg(Color::DarkGray)
}

/// The always-visible summary row for a character.
fn summary_line(data: &CharacterData) -> Line<'static> {
    let mut spans = vec![
        Span::raw(format!("{:>3} ", data.chara_id.value())),
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

fn detail_lines(chara: &Character, data: &CharacterData) -> Vec<Line<'static>> {
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

    vec![
        detail("Type ID", data.chara_type_id.to_string()),
        detail(
            "Footing",
            labeled_constant(data.footing.value(), data.footing.constant_name()),
        ),
        detail(
            "Friend",
            format!("{} ({})", data.friend_flag.value(), data.friend_flag.display_name()),
        ),
        detail("Level", data.level.to_string()),
        detail(
            "Weapon",
            format!(
                "id {} (equipped {}/{})",
                data.weapon_id, chara.equipped_weapon_index, chara.num_weapons
            ),
        ),
        detail(
            "Samurai/Battle",
            format!("{}/{}", data.samurai_value, data.battle_value),
        ),
        detail(
            "AI",
            format!(
                "{}  group {}",
                labeled_constant(chara.ai_mode.value(), chara.ai_mode.constant_name()),
                chara.ai_group_id
            ),
        ),
        detail(
            "Animation",
            labeled_constant(chara.animation_id.value(), chara.animation_id.constant_name()),
        ),
        detail(
            "Func",
            format!("cur {} last {}", chara.current_func_id, chara.last_func_id),
        ),
        detail("Held", chara.held_object.display_name().to_string()),
        detail(
            "Watch",
            format!(
                "{} -> {}",
                chara.watch_type.display_name(),
                chara.watched_chara_id.display_name()
            ),
        ),
        detail(
            "Pos",
            format!("{:.1}, {:.1}, {:.1}", position[0], position[1], position[2]),
        ),
        detail(
            "Special",
            format!("{}  throws {}", chara.special_state, chara.throw_count),
        ),
        detail("Events", events),
    ]
}

fn build_item(chara: &Character, data: &CharacterData, expanded: bool) -> ListItem<'static> {
    let mut lines = vec![summary_line(data)];
    if expanded {
        lines.extend(detail_lines(chara, data));
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
        .map(|(i, (chara, data))| build_item(chara, data, expanded.contains(&i)))
        .collect();

    let title = format!("Characters ({})", items.len());
    let list = List::new(items)
        .block(panel_block(title, focused))
        .highlight_symbol("> ")
        .highlight_style(Style::new().add_modifier(Modifier::BOLD));
    frame.render_stateful_widget(list, area, state);
}
