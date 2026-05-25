use std::time::{Duration, Instant};

use anyhow::Result;
use ratatui::{DefaultTerminal, Frame};

use crate::debug::*;

const REFRESH_INTERVAL: Duration = Duration::from_millis(3000);

pub struct DebuggerApp {
    debugger: Debugger,
    last_refresh: Instant,
}

impl DebuggerApp {
    pub fn new() -> Self {
        Self {
            debugger: Debugger::new(),
            last_refresh: Instant::now(),
        }
    }

    fn refresh(&mut self) -> Result<()> {
        let now = Instant::now();
        if (now - self.last_refresh) < REFRESH_INTERVAL {
            return Ok(());
        }
        self.debugger.update()?;
        self.last_refresh = now;
        Ok(())
    }

    pub fn run(&mut self, terminal: &mut DefaultTerminal) -> Result<()> {
        loop {
            self.refresh()?;
            terminal.draw(|frame| self.draw(frame))?;
        }
        Ok(())
    }

    fn draw(&self, frame: &mut Frame) {
        if let Some(game) = self.debugger.game() {
            // TODO
            frame.render_widget("Game is running", frame.area());
        } else if self.debugger.is_emulator_running() {
            let message = format!(
                "Found PCSX2, PID: {}. Waiting for Way of the Samurai...",
                self.debugger.pid().unwrap()
            );
            frame.render_widget(message, frame.area());
        } else {
            frame.render_widget("Waiting for PCSX2...", frame.area());
        }
    }
}

pub fn run_debugger() -> Result<()> {
    let mut app = DebuggerApp::new();
    ratatui::run(|term| app.run(term))?;
    Ok(())
}
