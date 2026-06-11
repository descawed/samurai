use ratatui::Frame;
use ratatui::layout::Rect;
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::Paragraph;

use crate::debug::Game;

use super::panel_block;

fn vector_row<'a>(label: &'static str, v: [f32; 3]) -> Line<'a> {
    Line::from(vec![
        Span::styled(format!("{label:>5}: "), Style::new().add_modifier(Modifier::BOLD)),
        Span::raw(format!("{:8.2} {:8.2} {:8.2}", v[0], v[1], v[2])),
    ])
}

pub fn render(frame: &mut Frame, area: Rect, game: &Game, focused: bool) {
    let lines = match game.free_cam() {
        Some(camera) => vec![
            Line::from(Span::styled(
                "ON",
                Style::new().fg(Color::Green).add_modifier(Modifier::BOLD),
            )),
            vector_row("pos", camera.position()),
            vector_row("look", camera.look()),
            Line::from(""),
            Line::from("WASD: move   QE: down/up").style(Style::new().add_modifier(Modifier::DIM)),
            Line::from("arrows: look   Shift: fast").style(Style::new().add_modifier(Modifier::DIM)),
        ],
        None => vec![
            Line::from(Span::styled("OFF", Style::new().add_modifier(Modifier::DIM))),
            Line::from(""),
            Line::from("press f to enable free camera")
                .style(Style::new().add_modifier(Modifier::DIM)),
        ],
    };

    frame.render_widget(Paragraph::new(lines).block(panel_block("Camera", focused)), area);
}
