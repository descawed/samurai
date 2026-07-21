use std::collections::HashSet;
use std::fmt::{Display, UpperHex};
use std::time::{Duration, Instant};

use anyhow::Result;
use crossterm::{execute, terminal::SetTitle};
use ratatui::crossterm::event::{self, Event, KeyCode, KeyEvent, KeyEventKind, KeyModifiers};
use ratatui::layout::{Constraint, Layout, Rect};
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::Line;
use ratatui::widgets::{Block, ListState, Paragraph, Tabs};
use ratatui::{DefaultTerminal, Frame};

use crate::debug::*;

mod camera;
mod characters;
mod config;
mod flags;
mod globals;

use config::Config;
use flags::FlagCategory;

const REFRESH_INTERVAL: Duration = Duration::from_millis(3000);
/// How long to wait for input before redrawing. Kept well below `REFRESH_INTERVAL` so the data
/// stays current even when the user isn't pressing anything.
const POLL_INTERVAL: Duration = Duration::from_millis(200);

/// Minimum terminal size required to show all three panels at once. Below this we fall back to a
/// single, tabbed panel.
const MIN_WIDE_WIDTH: u16 = 70;
const MIN_WIDE_HEIGHT: u16 = 16;
/// Width of the flags panel in the wide layout. Flag rows are short (the widest is a pro-flag
/// constant name), so we cap the panel and let the left column take the remaining width.
const FLAGS_WIDTH: u16 = 34;
/// Height of the globals panel in the wide layout (12 rows + borders).
const GLOBALS_HEIGHT: u16 = 14;
/// Height of the camera panel in the wide layout (6 rows + borders).
const CAMERA_HEIGHT: u16 = 8;

/// Distance the free camera moves per keypress, and the larger step when Shift is held. Movement is
/// discrete (terminals have no key-up event), so these are tuned for comfortable key-repeat rather
/// than a per-second rate.
const MOVE_STEP: f32 = 0.5;
const FAST_MOVE_STEP: f32 = 2.0;
/// Radians the free camera turns per keypress, normal and fast.
const TURN_STEP: f32 = 0.04;
const FAST_TURN_STEP: f32 = 0.16;

/// Border color for the panel that currently has focus.
const FOCUS_COLOR: Color = Color::Cyan;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Focus {
    Globals,
    Characters,
    Flags,
    Camera,
}

impl Focus {
    const ALL: [Focus; 4] = [Focus::Globals, Focus::Characters, Focus::Flags, Focus::Camera];

    fn index(self) -> usize {
        Self::ALL.iter().position(|f| *f == self).unwrap()
    }

    fn cycle(self, forward: bool) -> Self {
        let len = Self::ALL.len();
        let offset = if forward { 1 } else { len - 1 };
        Self::ALL[(self.index() + offset) % len]
    }
}

/// All transient UI state (focus, scroll offsets, selections). Kept separate from `DebuggerApp` so
/// it can be borrowed mutably while the game data is borrowed immutably.
struct UiState {
    focus: Focus,
    globals_scroll: u16,
    characters: ListState,
    /// Character list indices that are currently expanded to show detail.
    expanded: HashSet<usize>,
    flag_category: FlagCategory,
    /// Independent scroll/selection state for each flag category.
    flags: [ListState; FlagCategory::ALL.len()],
}

impl Default for UiState {
    fn default() -> Self {
        Self {
            focus: Focus::Globals,
            globals_scroll: 0,
            characters: ListState::default(),
            expanded: HashSet::new(),
            flag_category: FlagCategory::Man,
            flags: Default::default(),
        }
    }
}

pub struct DebuggerApp {
    debugger: Debugger,
    config: Config,
    last_refresh: Instant,
    /// The `(version, phase, event)` last evaluated for the "New" label, used to detect when the
    /// current event changes.
    last_event: Option<(&'static str, i8, i32)>,
    /// Whether the current `(phase, event)` had not been seen before for this game version. Set
    /// when the event changes and shown next to the event ID until the next change.
    event_is_new: bool,
    ui: UiState,
    should_quit: bool,
}

impl Default for DebuggerApp {
    fn default() -> Self {
        Self::new()
    }
}

impl DebuggerApp {
    pub fn new() -> Self {
        Self {
            debugger: Debugger::new(),
            config: Config::load(),
            // place the last refresh in the past so the first frame loads data immediately
            last_refresh: Instant::now()
                .checked_sub(REFRESH_INTERVAL)
                .unwrap_or_else(Instant::now),
            last_event: None,
            event_is_new: false,
            ui: UiState::default(),
            should_quit: false,
        }
    }

    fn refresh(&mut self) -> Result<()> {
        let now = Instant::now();
        if (now - self.last_refresh) < REFRESH_INTERVAL {
            return Ok(());
        }
        self.debugger.update()?;
        self.last_refresh = now;
        self.update_event_status();
        Ok(())
    }

    /// After a refresh, decide whether the current `(phase, event)` is new for the running game
    /// version. Recording a newly-seen pair persists it to the config. The "New" label stays until
    /// the phase or event changes.
    fn update_event_status(&mut self) {
        let Some((version, phase, event)) = self.debugger.game().map(|game| {
            (game.version_name(), game.game_state.phase_id, game.game_state.event_id)
        }) else {
            // no game running; reset so a freshly-attached game is re-evaluated
            self.last_event = None;
            self.event_is_new = false;
            return;
        };

        if self.last_event != Some((version, phase, event)) {
            self.event_is_new = self.config.mark_event_seen(version, phase, event);
            self.last_event = Some((version, phase, event));
        }
    }

    pub fn run(&mut self, terminal: &mut DefaultTerminal) -> Result<()> {
        while !self.should_quit {
            self.refresh()?;
            terminal.draw(|frame| self.draw(frame))?;
            if event::poll(POLL_INTERVAL)? && let Event::Key(key) = event::read()? {
                self.handle_key(key)?;
            }
        }
        Ok(())
    }

    fn handle_key(&mut self, key: KeyEvent) -> Result<()> {
        // ignore key-release events on terminals that report them
        if key.kind == KeyEventKind::Release {
            return Ok(());
        }

        // keys that apply regardless of focus
        match (key.code, key.modifiers) {
            (KeyCode::Char('c'), KeyModifiers::CONTROL) | (KeyCode::Esc, _) => {
                self.should_quit = true;
                return Ok(());
            }
            (KeyCode::Char('f'), _) => return self.toggle_free_cam(),
            (KeyCode::Tab, _) => {
                self.ui.focus = self.ui.focus.cycle(true);
                return Ok(());
            }
            (KeyCode::BackTab, _) => {
                self.ui.focus = self.ui.focus.cycle(false);
                return Ok(());
            }
            _ => {}
        }

        // while the camera panel is focused and free cam is active, movement keys drive the camera
        // instead of the usual panel navigation
        if self.ui.focus == Focus::Camera && self.handle_camera_key(key)? {
            return Ok(());
        }

        match (key.code, key.modifiers) {
            (KeyCode::Char('q'), _) => self.should_quit = true,
            (KeyCode::Down | KeyCode::Char('j'), _) => self.move_by(1),
            (KeyCode::Up | KeyCode::Char('k'), _) => self.move_by(-1),
            (KeyCode::PageDown, _) => self.move_by(10),
            (KeyCode::PageUp, _) => self.move_by(-10),
            (KeyCode::Enter | KeyCode::Char(' '), _) => self.toggle_expand(),
            (KeyCode::Right | KeyCode::Char('l'), _) => self.cycle_category(true),
            (KeyCode::Left | KeyCode::Char('h'), _) => self.cycle_category(false),
            _ => {}
        }
        Ok(())
    }

    /// Toggle free camera mode. When turning it on, switch focus to the camera panel so its movement
    /// keys are live.
    fn toggle_free_cam(&mut self) -> Result<()> {
        if let Some(game) = self.debugger.game_mut()
            && game.toggle_free_cam()?
        {
            self.ui.focus = Focus::Camera;
        }
        Ok(())
    }

    /// Drive the free camera from a movement key. Returns whether the key was consumed (only when
    /// free cam is active and the key maps to a camera action).
    fn handle_camera_key(&mut self, key: KeyEvent) -> Result<bool> {
        let fast = key.modifiers.contains(KeyModifiers::SHIFT);
        let move_step = if fast { FAST_MOVE_STEP } else { MOVE_STEP };
        let turn_step = if fast { FAST_TURN_STEP } else { TURN_STEP };

        let Some(game) = self.debugger.game_mut() else {
            return Ok(false);
        };
        if !game.is_free_cam() {
            return Ok(false);
        }

        // Shift typically uppercases the reported character, so accept both cases
        match key.code {
            KeyCode::Char('w' | 'W') => game.adjust_free_cam(|c| c.dolly(move_step))?,
            KeyCode::Char('s' | 'S') => game.adjust_free_cam(|c| c.dolly(-move_step))?,
            KeyCode::Char('a' | 'A') => game.adjust_free_cam(|c| c.strafe(-move_step))?,
            KeyCode::Char('d' | 'D') => game.adjust_free_cam(|c| c.strafe(move_step))?,
            KeyCode::Char('e' | 'E') => game.adjust_free_cam(|c| c.rise(move_step))?,
            KeyCode::Char('q' | 'Q') => game.adjust_free_cam(|c| c.rise(-move_step))?,
            KeyCode::Left => game.adjust_free_cam(|c| c.yaw(turn_step))?,
            KeyCode::Right => game.adjust_free_cam(|c| c.yaw(-turn_step))?,
            KeyCode::Up => game.adjust_free_cam(|c| c.pitch(turn_step))?,
            KeyCode::Down => game.adjust_free_cam(|c| c.pitch(-turn_step))?,
            _ => return Ok(false),
        }
        Ok(true)
    }

    /// Move the selection/scroll within the focused panel by `delta` rows.
    fn move_by(&mut self, delta: i32) {
        match self.ui.focus {
            Focus::Globals => {
                let scroll = self.ui.globals_scroll as i32 + delta;
                // the upper bound is clamped against the viewport at render time
                self.ui.globals_scroll = scroll.max(0) as u16;
            }
            Focus::Characters => {
                let len = self.debugger.game().map_or(0, |g| g.iter_characters().count());
                move_selection(&mut self.ui.characters, len, delta);
            }
            Focus::Flags => {
                let category = self.ui.flag_category;
                move_selection(&mut self.ui.flags[category.index()], category.len(), delta);
            }
            // the camera panel has nothing to scroll; movement is handled by handle_camera_key
            Focus::Camera => {}
        }
    }

    fn toggle_expand(&mut self) {
        if self.ui.focus != Focus::Characters {
            return;
        }
        if let Some(selected) = self.ui.characters.selected()
            && !self.ui.expanded.remove(&selected)
        {
            self.ui.expanded.insert(selected);
        }
    }

    fn cycle_category(&mut self, forward: bool) {
        if self.ui.focus == Focus::Flags {
            self.ui.flag_category = self.ui.flag_category.cycle(forward);
        }
    }

    fn draw(&mut self, frame: &mut Frame) {
        let area = frame.area();
        if let Some(game) = self.debugger.game() {
            draw_running(frame, area, game, &mut self.ui, self.event_is_new);
        } else if self.debugger.is_emulator_running() {
            let message = format!(
                "Found {}, PID: {}. Waiting for Way of the Samurai...",
                self.debugger.emulator_name().unwrap_or("emulator"),
                self.debugger.pid().unwrap()
            );
            frame.render_widget(Paragraph::new(message), area);
        } else {
            frame.render_widget(Paragraph::new("Waiting for PCSX2 or PPSSPP..."), area);
        }
    }
}

fn draw_running(frame: &mut Frame, area: Rect, game: &Game, ui: &mut UiState, event_is_new: bool) {
    let [body, footer] =
        Layout::vertical([Constraint::Min(0), Constraint::Length(1)]).areas(area);

    if area.width >= MIN_WIDE_WIDTH && area.height >= MIN_WIDE_HEIGHT {
        draw_wide(frame, body, game, ui, event_is_new);
    } else {
        draw_tabbed(frame, body, game, ui, event_is_new);
    }

    frame.render_widget(footer_hint(ui.focus), footer);
}

/// All panels at once: globals over characters on the left; flags over the camera on the right.
fn draw_wide(frame: &mut Frame, area: Rect, game: &Game, ui: &mut UiState, event_is_new: bool) {
    let [left, right] =
        Layout::horizontal([Constraint::Min(0), Constraint::Length(FLAGS_WIDTH)]).areas(area);
    let [globals_area, characters_area] =
        Layout::vertical([Constraint::Length(GLOBALS_HEIGHT), Constraint::Min(0)]).areas(left);
    let [flags_area, camera_area] =
        Layout::vertical([Constraint::Min(0), Constraint::Length(CAMERA_HEIGHT)]).areas(right);

    globals::render(
        frame,
        globals_area,
        game,
        &mut ui.globals_scroll,
        ui.focus == Focus::Globals,
        event_is_new,
    );
    characters::render(
        frame,
        characters_area,
        game,
        &mut ui.characters,
        &ui.expanded,
        ui.focus == Focus::Characters,
    );
    let category = ui.flag_category;
    flags::render(
        frame,
        flags_area,
        game,
        category,
        &mut ui.flags[category.index()],
        ui.focus == Focus::Flags,
    );
    camera::render(frame, camera_area, game, ui.focus == Focus::Camera);
}

/// A single panel, chosen by the focused section, under a tab bar.
fn draw_tabbed(frame: &mut Frame, area: Rect, game: &Game, ui: &mut UiState, event_is_new: bool) {
    let [tabs_area, panel] =
        Layout::vertical([Constraint::Length(1), Constraint::Min(0)]).areas(area);

    let tabs = Tabs::new(["Globals", "Characters", "Flags", "Camera"])
        .select(ui.focus.index())
        .highlight_style(Style::new().fg(FOCUS_COLOR).add_modifier(Modifier::BOLD));
    frame.render_widget(tabs, tabs_area);

    match ui.focus {
        Focus::Globals => {
            globals::render(frame, panel, game, &mut ui.globals_scroll, true, event_is_new)
        }
        Focus::Characters => {
            characters::render(frame, panel, game, &mut ui.characters, &ui.expanded, true)
        }
        Focus::Flags => {
            let category = ui.flag_category;
            flags::render(frame, panel, game, category, &mut ui.flags[category.index()], true)
        }
        Focus::Camera => camera::render(frame, panel, game, true),
    }
}

fn footer_hint(focus: Focus) -> Line<'static> {
    let keys = match focus {
        Focus::Globals => "Tab: panel   ↑↓: scroll   f: free cam   q: quit",
        Focus::Characters => "Tab: panel   ↑↓: move   Enter: expand   f: free cam   q: quit",
        Focus::Flags => "Tab: panel   ↑↓: move   ←→: category   f: free cam   q: quit",
        Focus::Camera => "Tab: panel   WASD/QE: move   arrows: look   Shift: fast   f: toggle",
    };
    Line::from(keys).style(Style::new().add_modifier(Modifier::DIM))
}

/// A bordered block whose border is highlighted when `focused`.
fn panel_block<'a>(title: impl Into<Line<'a>>, focused: bool) -> Block<'a> {
    let block = Block::bordered().title(title.into());
    if focused {
        block.border_style(Style::new().fg(FOCUS_COLOR).add_modifier(Modifier::BOLD))
    } else {
        block
    }
}

/// Move a list selection by `delta`, clamped to `[0, len)`. Clears the selection for an empty list.
fn move_selection(state: &mut ListState, len: usize, delta: i32) {
    if len == 0 {
        state.select(None);
        return;
    }
    // the first key press selects the first row rather than stepping past it
    let next = match state.selected() {
        None => 0,
        Some(current) => (current as i32 + delta).clamp(0, len as i32 - 1) as usize,
    };
    state.select(Some(next));
}

/// Formats a constant-backed value as `value (CONSTANT_NAME)`, falling back to just the value when
/// there is no associated constant name.
fn labeled_constant<I: Display>(value: I, name: Option<&str>) -> String {
    match name {
        Some(name) => format!("{value} ({name})"),
        None => format!("{value}"),
    }
}

fn labeled_constant_hex<I: Display + UpperHex>(value: I, name: Option<&str>) -> String {
    match name {
        Some(name) => format!("{value:08X} ({name})"),
        None => format!("{value:08X}"),
    }
}

pub fn run_debugger() -> Result<()> {
    execute!(std::io::stdout(), SetTitle("Way of the Samurai debugger"))?;

    let mut app = DebuggerApp::new();
    ratatui::run(|term| app.run(term))?;
    Ok(())
}
