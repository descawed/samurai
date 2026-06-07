use std::time::Duration;

use log::LevelFilter;
use lss_autosplitter::{AutoSplitter, Config, LiveSplitConfig};

use crate::autosplitter::SamuraiGame;

/// Run the autosplitter, blocking until a fatal error occurs.
pub fn run_autosplitter(
    live_split_port: u16,
    update_frequency: u64,
    ending: Option<u8>,
    new_game_plus: Option<bool>,
    log_level: LevelFilter,
) -> anyhow::Result<()> {
    colog::default_builder().filter_level(log_level).init();

    let config = Config {
        live_split: LiveSplitConfig {
            port: live_split_port,
            ..Default::default()
        },
        update_frequency: Duration::from_millis(update_frequency),
        ..Default::default()
    };

    let game = SamuraiGame::new(ending, new_game_plus);
    let mut splitter = AutoSplitter::new(game, config);
    splitter.run()?;
    Ok(())
}
