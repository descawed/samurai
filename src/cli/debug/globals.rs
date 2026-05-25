use ratatui::Frame;
use ratatui::layout::Rect;
use ratatui::style::{Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::Paragraph;

use crate::debug::*;

use super::{labeled_constant, panel_block};

/// Builds one `label: value` row.
fn row<'a>(label: &'static str, value: String) -> Line<'a> {
    Line::from(vec![
        Span::styled(format!("{label:>10}: "), Style::new().add_modifier(Modifier::BOLD)),
        Span::raw(value),
    ])
}

fn build_lines(game: &Game) -> Vec<Line<'static>> {
    let state = &game.game_state;
    vec![
        row("Version", game.version_name().to_string()),
        row(
            "Difficulty",
            format!("{} ({})", state.difficulty.value(), state.difficulty.display_name()),
        ),
        row("Phase", state.phase_id.to_string()),
        row("Event", state.event_id.to_string()),
        row("Map", labeled_constant(state.map_id.value(), state.map_id.constant_name())),
        row("Exit", state.exit_id.to_string()),
        row(
            "Map Time",
            labeled_constant(state.map_time_id.value(), state.map_time_id.constant_name()),
        ),
        row(
            "Footing",
            labeled_constant(state.player_footing.value(), state.player_footing.constant_name()),
        ),
        row("Money", state.player_money.to_string()),
        row("Kills", state.player_num_kills.to_string()),
        row("GP", state.gp.to_string()),
    ]
}

pub fn render(frame: &mut Frame, area: Rect, game: &Game, scroll: &mut u16, focused: bool) {
    let lines = build_lines(game);

    // clamp the scroll offset against the content so we never scroll past the last row
    let viewport = area.height.saturating_sub(2); // account for the borders
    let max_scroll = (lines.len() as u16).saturating_sub(viewport);
    *scroll = (*scroll).min(max_scroll);

    let paragraph = Paragraph::new(lines)
        .block(panel_block("Globals", focused))
        .scroll((*scroll, 0));
    frame.render_widget(paragraph, area);
}
