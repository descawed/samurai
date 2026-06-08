use std::cell::RefCell;
use std::time::Duration;
use sysinfo::Pid;
use thiserror::Error;

mod constants;
pub use constants::*;
mod emulator;
use emulator::*;
mod game;
pub use game::*;
mod platform;
use platform::*;

const PROCESS_REFRESH_INTERVAL: Duration = Duration::from_millis(2000);

#[derive(Error, Debug)]
pub enum DebugError {
    #[error("emulator memory error")]
    EmulatorMemoryError(#[from] std::io::Error),
    #[error("failed to parse game data")]
    DataParseError(#[from] binrw::Error),
    #[error("player exited the game")]
    GameLost,
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

pub type Result<T> = std::result::Result<T, DebugError>;

enum State {
    WaitingForEmulator,
    WaitingForGame(Emulator),
    GameRunning(Game),
}

impl Default for State {
    fn default() -> Self {
        Self::WaitingForEmulator
    }
}

pub struct Debugger {
    platform: RefCell<Platform>,
    state: State,
    /// When set, `update` skips reading the (large) character data, saving time for consumers that
    /// don't need it (e.g. the autosplitter).
    skip_characters: bool,
}

impl Debugger {
    pub fn new() -> Self {
        Self::with_options(false)
    }

    /// Create a debugger, optionally skipping the character data when updating. See
    /// [`Game::update_with`].
    pub fn with_options(skip_characters: bool) -> Self {
        Self {
            platform: RefCell::new(Platform::new(PROCESS_REFRESH_INTERVAL)),
            state: State::WaitingForEmulator,
            skip_characters,
        }
    }

    fn map_error(&self, err: DebugError, pid: Pid) -> Result<State> {
        if matches!(err, DebugError::EmulatorMemoryError(_)) && !self.is_pid_alive(pid) {
            Ok(State::WaitingForEmulator)
        } else {
            Err(err)
        }
    }

    fn wait_for_game(&self, emulator: Emulator) -> Result<State> {
        let search_result = GameVersion::search_for_version(&emulator);
        Ok(match search_result {
            Ok(Some(version)) => self.update_game(Game::new(version, emulator))?,
            Ok(None) => State::WaitingForGame(emulator),
            Err(err) => self.map_error(err, emulator.pid())?,
        })
    }

    fn update_game(&self, mut game: Game) -> Result<State> {
        let update_result = game.update_with(self.skip_characters);
        Ok(match update_result {
            Ok(()) => State::GameRunning(game),
            Err(DebugError::GameLost) => State::WaitingForGame(game.detach()),
            Err(err) => self.map_error(err, game.pid())?,
        })
    }

    pub fn update(&mut self) -> Result<()> {
        self.state = match std::mem::take(&mut self.state) {
            State::WaitingForEmulator => {
                match Emulator::search_for_emulator(self.platform.borrow()) {
                    Some(emulator) => self.wait_for_game(emulator)?,
                    None => State::WaitingForEmulator,
                }
            }
            State::WaitingForGame(emulator) => self.wait_for_game(emulator)?,
            State::GameRunning(game) => self.update_game(game)?,
        };

        Ok(())
    }

    pub fn pid(&self) -> Option<Pid> {
        match &self.state {
            State::WaitingForEmulator => None,
            State::WaitingForGame(emulator) => Some(emulator.pid()),
            State::GameRunning(game) => Some(game.pid()),
        }
    }

    fn is_pid_alive(&self, pid: Pid) -> bool {
        // if we fail to mutably borrow the platform, we just ignore it; it's not the end of the
        // world if the data's a little stale
        if let Ok(mut platform) = self.platform.try_borrow_mut() {
            platform.refresh_if_stale();
        }
        self.platform.borrow().is_pid_alive(pid)
    }

    pub fn is_emulator_running(&self) -> bool {
        match self.pid() {
            Some(pid) => self.is_pid_alive(pid),
            None => false,
        }
    }

    pub fn game(&self) -> Option<&Game> {
        match &self.state {
            State::GameRunning(game) => Some(game),
            _ => None,
        }
    }

    pub fn game_mut(&mut self) -> Option<&mut Game> {
        match &mut self.state {
            State::GameRunning(game) => Some(game),
            _ => None,
        }
    }

    /// Read a single character's [`CharacterData`] on demand, identified by its index (a `CHID_`
    /// value) in the character data array. Returns `None` if no game is currently running. This
    /// works even when the debugger is configured to skip character data on update; see
    /// [`Game::read_character_data`].
    pub fn read_character_data(&self, id: usize) -> Result<Option<CharacterData>> {
        match &self.state {
            State::GameRunning(game) => game.read_character_data(id).map(Some),
            _ => Ok(None),
        }
    }
}
