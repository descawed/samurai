use ratatui::Frame;
use ratatui::layout::{Constraint, Layout, Rect};
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::Line;
use ratatui::widgets::{List, ListItem, ListState, Tabs};

use crate::debug::*;

use super::{FOCUS_COLOR, panel_block};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlagCategory {
    Man,
    Pro,
    Int,
    Act,
}

impl FlagCategory {
    pub const ALL: [FlagCategory; 4] =
        [FlagCategory::Man, FlagCategory::Pro, FlagCategory::Int, FlagCategory::Act];

    pub fn index(self) -> usize {
        Self::ALL.iter().position(|c| *c == self).unwrap()
    }

    pub fn cycle(self, forward: bool) -> Self {
        let len = Self::ALL.len();
        let offset = if forward { 1 } else { len - 1 };
        Self::ALL[(self.index() + offset) % len]
    }

    /// The number of entries in this category.
    pub fn len(self) -> usize {
        match self {
            FlagCategory::Man => 128,
            FlagCategory::Pro => 32,
            FlagCategory::Int => 256,
            FlagCategory::Act => 32,
        }
    }

    fn tab_label(self) -> &'static str {
        match self {
            FlagCategory::Man => "Man",
            FlagCategory::Pro => "Pro",
            FlagCategory::Int => "Int",
            FlagCategory::Act => "Act",
        }
    }
}

/// Builds one flag row. Rows with a zero value are dimmed; `name` adds a `(CONSTANT)` suffix.
fn flag_item(index: usize, value: i64, name: Option<&str>) -> ListItem<'static> {
    let label = match name {
        Some(name) => format!("{index:>3}: {value} ({name})"),
        None => format!("{index:>3}: {value}"),
    };
    let style = if value == 0 {
        Style::new().fg(Color::DarkGray)
    } else {
        Style::new()
    };
    ListItem::new(Line::from(label)).style(style)
}

fn build_items(game: &Game, category: FlagCategory) -> Vec<ListItem<'static>> {
    let state = &game.game_state;
    match category {
        FlagCategory::Man => state
            .event_man_flags
            .iter()
            .enumerate()
            .map(|(i, &v)| flag_item(i, v as i64, None))
            .collect(),
        FlagCategory::Pro => state
            .event_pro_flags
            .iter()
            .enumerate()
            .map(|(i, p)| flag_item(i, p.value() as i64, p.constant_name()))
            .collect(),
        FlagCategory::Int => state
            .int_vars
            .iter()
            .enumerate()
            .map(|(i, &v)| flag_item(i, v as i64, None))
            .collect(),
        FlagCategory::Act => state
            .event_act_end_flags
            .iter()
            .enumerate()
            .map(|(i, &v)| flag_item(i, v as i64, None))
            .collect(),
    }
}

pub fn render(
    frame: &mut Frame,
    area: Rect,
    game: &Game,
    category: FlagCategory,
    state: &mut ListState,
    focused: bool,
) {
    let block = panel_block("Flags", focused);
    let inner = block.inner(area);
    frame.render_widget(block, area);

    let [tabs_area, list_area] =
        Layout::vertical([Constraint::Length(1), Constraint::Min(0)]).areas(inner);

    let tabs = Tabs::new(FlagCategory::ALL.map(|c| c.tab_label()))
        .select(category.index())
        .highlight_style(Style::new().fg(FOCUS_COLOR).add_modifier(Modifier::BOLD));
    frame.render_widget(tabs, tabs_area);

    let list = List::new(build_items(game, category))
        .highlight_symbol("> ")
        .highlight_style(Style::new().add_modifier(Modifier::BOLD));
    frame.render_stateful_widget(list, list_area, state);
}
