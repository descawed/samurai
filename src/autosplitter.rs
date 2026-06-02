//! A [LiveSplit] autosplitter for speedruns of (Way of the) Samurai running in PCSX2.
//!
//! The autosplitter drives a LiveSplit timer based on the live state of the game, read through the
//! [`Debugger`]. The run category is determined by the target ending (1-6) and whether the run is
//! New Game (NG) or New Game+ (NG+). These can be supplied on the command line or read from custom
//! variables in the LiveSplit splits; a command-line value always overrides the LiveSplit value.
//! The category selects a [`Route`](routes::Route) — a sequence of game events to split on. With no
//! route, the autosplitter splits on every event change instead.
//!
//! LiveSplit is treated as the source of truth: the timer phase and split index are read from it
//! every poll rather than tracked internally, so the autosplitter stays in agreement with whatever
//! the runner does to the timer.
//!
//! [LiveSplit]: https://livesplit.org/

use lss_autosplitter::{Error, Game as LssGame, GameStatus, LiveSplit, Result, TimerPhase};

use crate::debug::{CharacterMenuMode, Debugger, EngineMode, Game, MainMenu, MenuMode};

pub mod routes;
use routes::{Category, Route, route_for};

/// Name of the LiveSplit custom variable holding the target ending (1-6).
const ENDING_VARIABLE_NAME: &str = "SamuraiEnding";
/// Name of the LiveSplit custom variable holding the new game type (NG or NG+).
const NEW_GAME_VARIABLE_NAME: &str = "SamuraiNewGame";

/// How many polls between re-reads of the LiveSplit category variables. At the default 15 ms update
/// frequency this is roughly five seconds.
const CATEGORY_SYNC_PERIOD: i32 = 334;

/// A simple down-counter used to throttle periodic work (re-reading the category from LiveSplit)
/// rather than doing it on every poll.
#[derive(Debug, Clone)]
struct PeriodicCheck {
    period: i32,
    remaining: i32,
}

impl PeriodicCheck {
    /// Create a counter that fires on its first [`should_check`](Self::should_check).
    const fn new(period: i32) -> Self {
        Self { period, remaining: 0 }
    }

    /// Arrange for the next [`should_check`](Self::should_check) to return `true`.
    const fn force_check(&mut self) {
        self.remaining = 0;
    }

    const fn should_check(&mut self) -> bool {
        if self.remaining <= 0 {
            self.remaining = self.period;
            true
        } else {
            self.remaining -= 1;
            false
        }
    }
}

/// Parse a new game type value into a "is new game plus" flag. Accepts a handful of spellings so it
/// works for both command-line and LiveSplit-supplied values.
fn parse_new_game_plus(value: &str) -> Option<bool> {
    match value.trim().to_ascii_lowercase().as_str() {
        "ng" | "new game" | "new-game" | "newgame" => Some(false),
        "ng+" | "ngplus" | "ng plus" | "new game+" | "new game plus" | "new-game-plus" => Some(true),
        _ => None,
    }
}

fn category_label(category: Category) -> String {
    format!(
        "ending {} ({})",
        category.ending,
        if category.new_game_plus { "NG+" } else { "NG" }
    )
}

fn get_live_split_ending(live_split: &mut LiveSplit) -> Result<Option<u8>> {
    let Some(value) = live_split.get_custom_variable_value(ENDING_VARIABLE_NAME)? else {
        return Ok(None);
    };

    match value.trim().parse::<u8>() {
        Ok(ending @ 1..=6) => Ok(Some(ending)),
        _ => {
            log::warn!("LiveSplit reported invalid ending {value:?}; ignoring");
            Ok(None)
        }
    }
}

fn get_live_split_new_game_plus(live_split: &mut LiveSplit) -> Result<Option<bool>> {
    let Some(value) = live_split.get_custom_variable_value(NEW_GAME_VARIABLE_NAME)? else {
        return Ok(None);
    };

    match parse_new_game_plus(&value) {
        Some(new_game_plus) => Ok(Some(new_game_plus)),
        None => {
            log::warn!("LiveSplit reported unrecognized new game type {value:?}; ignoring");
            Ok(None)
        }
    }
}

/// Whether the engine is in a mode that's valid for a run to continue. Leaving these modes while
/// the timer is running means the run was abandoned (e.g. the player quit to the title screen), so
/// the timer should be reset.
fn is_valid_run_mode(game: &Game) -> bool {
    match game.engine.mode() {
        EngineMode::InGame
        | EngineMode::Loading
        | EngineMode::SaveCheckpoint
        | EngineMode::PhaseChange => true,
        EngineMode::MainMenu => matches!(
            game.main_menu().map(MainMenu::menu_mode),
            Some(
                MenuMode::OverwriteSaveData
                    | MenuMode::NewGameCharacterMenu
                    | MenuMode::SaveGame
                    | MenuMode::ContinueFromSave
            )
        ),
        _ => false,
    }
}

/// Whether the player has just confirmed a new game from the character creation menu, which is our
/// cue to start the timer.
fn is_new_game_start(game: &Game) -> bool {
    game.new_game_character_menu()
        .is_some_and(|menu| menu.next_mode() == CharacterMenuMode::StartNewGame)
}

/// The Way of the Samurai [`Game`](LssGame) implementation.
pub struct SamuraiGame {
    debugger: Debugger,
    /// Ending requested on the command line, overriding any LiveSplit value.
    requested_ending: Option<u8>,
    /// New game type requested on the command line, overriding any LiveSplit value.
    requested_new_game_plus: Option<bool>,
    /// The category currently in effect, if it could be determined.
    category: Option<Category>,
    /// The route for the current category, if one is defined.
    route: Option<&'static Route>,
    /// The last `(phase ID, event ID)` we observed, used to detect event transitions.
    last_event: Option<(i8, i32)>,
    /// Throttles re-reading the category variables from LiveSplit.
    category_sync: PeriodicCheck,
}

impl SamuraiGame {
    pub fn new(requested_ending: Option<u8>, requested_new_game_plus: Option<bool>) -> Self {
        Self {
            // the autosplitter never needs character data, so skip it to keep the update loop cheap
            debugger: Debugger::with_options(true),
            requested_ending,
            requested_new_game_plus,
            category: None,
            route: None,
            last_event: None,
            category_sync: PeriodicCheck::new(CATEGORY_SYNC_PERIOD),
        }
    }

    /// Re-read the category from the command-line overrides and/or LiveSplit, updating the selected
    /// route if it changed.
    fn sync_category(&mut self, live_split: &mut LiveSplit) -> Result<()> {
        let ending = match self.requested_ending {
            Some(ending) => Some(ending),
            None => get_live_split_ending(live_split)?,
        };
        let new_game_plus = match self.requested_new_game_plus {
            Some(new_game_plus) => Some(new_game_plus),
            None => get_live_split_new_game_plus(live_split)?,
        };

        let category = match (ending, new_game_plus) {
            (Some(ending), Some(new_game_plus)) => Some(Category::new(ending, new_game_plus)),
            _ => None,
        };

        if category == self.category {
            return Ok(());
        }
        self.category = category;

        match category {
            Some(category) => {
                self.route = route_for(category);
                if self.route.is_some() {
                    log::info!("Using route for {}", category_label(category));
                } else {
                    log::warn!(
                        "No route defined for {}; splitting on every event change",
                        category_label(category)
                    );
                }
            }
            None => {
                self.route = None;
                log::warn!(
                    "Run category could not be determined; splitting on every event change"
                );
            }
        }

        Ok(())
    }
}

impl LssGame for SamuraiGame {
    fn connect(&mut self, _live_split: &mut LiveSplit) -> Result<()> {
        self.debugger.update().map_err(Error::game)?;
        if self.debugger.game().is_some() {
            Ok(())
        } else if self.debugger.is_emulator_running() {
            Err(Error::game("found PCSX2; waiting for Way of the Samurai"))
        } else {
            Err(Error::game("waiting for PCSX2"))
        }
    }

    fn live_split_connected(&mut self, _live_split: &mut LiveSplit) -> Result<()> {
        // re-sync the category with the freshly connected timer on the next poll
        self.category_sync.force_check();
        Ok(())
    }

    fn poll(&mut self, live_split: &mut LiveSplit) -> Result<GameStatus> {
        // periodically pick up category changes made in LiveSplit. if the read fails but the
        // connection is still up, it's presumably bogus data, so ignore it; only a dropped
        // connection is handed back to the framework as an error.
        if self.category_sync.should_check()
            && let Err(e) = self.sync_category(live_split)
            && !live_split.is_connected()
        {
            return Err(e);
        }

        if let Err(e) = self.debugger.update() {
            // the emulator or game went away; drop back to waiting for it
            log::debug!("Lost game: {e}");
            return Ok(GameStatus::Disconnected);
        }

        let Some(game) = self.debugger.game() else {
            // emulator is still up but no game is loaded; keep waiting unless it's gone entirely
            if self.debugger.is_emulator_running() {
                return Ok(GameStatus::Connected);
            }
            return Ok(GameStatus::Disconnected);
        };

        let current = (game.game_state.phase_id, game.game_state.event_id);

        match live_split.get_timer_phase()? {
            TimerPhase::NotRunning => {
                if is_new_game_start(game) {
                    log::info!("New game started; starting timer");
                    live_split.split()?;
                }
            }
            TimerPhase::Running | TimerPhase::Paused => {
                if !is_valid_run_mode(game) {
                    log::info!("Left a valid run state ({:?}); resetting", game.engine.mode());
                    live_split.reset()?;
                } else if Some(current) != self.last_event {
                    // we only act on the transition into a new (phase, event)
                    let should_split = match self.route {
                        Some(route) => {
                            let index = live_split.get_split_index()?;
                            usize::try_from(index)
                                .ok()
                                .and_then(|i| route.events().get(i))
                                .is_some_and(|next| *next == current)
                        }
                        // with no route, split on every event change
                        None => true,
                    };

                    if should_split {
                        log::debug!("Split (phase {}, event {})", current.0, current.1);
                        live_split.split()?;
                    }
                }
            }
            TimerPhase::Ended => {}
        }

        self.last_event = Some(current);
        Ok(GameStatus::Connected)
    }
}