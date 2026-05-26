use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};

/// Current config schema version. Bump when making an incompatible change to the file format so
/// older versions of the tool can detect it.
const CONFIG_VERSION: u32 = 1;

/// A `(phase, event)` pair the debugger has observed for a particular game version.
type SeenEvent = (i8, i32);

fn config_version() -> u32 {
    CONFIG_VERSION
}

/// User-specific debugger configuration, persisted to the platform's config directory
/// (e.g. `~/.config/samurai/config.toml` on Linux).
///
/// New settings can be added as additional fields; `#[serde(default)]` keeps older config files
/// loadable as the schema grows.
#[derive(Debug, Serialize, Deserialize)]
pub struct Config {
    /// Schema version, to support future migrations.
    #[serde(default = "config_version")]
    version: u32,
    /// `(phase, event)` pairs the debugger has seen, keyed by game version name.
    #[serde(default)]
    seen_events: BTreeMap<String, BTreeSet<SeenEvent>>,
    /// Path the config was loaded from and will be saved to. `None` disables persistence (e.g. when
    /// no config directory could be determined, or the existing file failed to parse and we don't
    /// want to clobber it). Not serialized.
    #[serde(skip)]
    path: Option<PathBuf>,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            version: CONFIG_VERSION,
            seen_events: BTreeMap::new(),
            path: None,
        }
    }
}

impl Config {
    /// The path to the user's config file, or `None` if no config directory is available.
    fn default_path() -> Option<PathBuf> {
        dirs::config_dir().map(|dir| dir.join("samurai").join("config.toml"))
    }

    /// Loads the config from the user's config directory. A missing file yields the defaults. If
    /// the file exists but can't be read or parsed, persistence is disabled for this session so the
    /// existing file isn't overwritten.
    pub fn load() -> Self {
        let Some(path) = Self::default_path() else {
            return Self::default();
        };

        if !path.exists() {
            return Self {
                path: Some(path),
                ..Self::default()
            };
        }

        match fs::read_to_string(&path).map_err(anyhow::Error::from).and_then(|text| {
            toml::from_str::<Config>(&text).map_err(anyhow::Error::from)
        }) {
            Ok(mut config) => {
                config.path = Some(path);
                config
            }
            // leave path as None to avoid clobbering an unreadable/corrupt file
            Err(_) => Self::default(),
        }
    }

    /// Writes the config to disk. A no-op when persistence is disabled (`path` is `None`).
    fn save(&self) -> Result<()> {
        let Some(path) = &self.path else {
            return Ok(());
        };

        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .with_context(|| format!("creating config directory {}", parent.display()))?;
        }

        let text = toml::to_string_pretty(self).context("serializing config")?;
        fs::write(path, text).with_context(|| format!("writing config to {}", path.display()))?;
        Ok(())
    }

    /// Records that `(phase, event)` was seen for the given game `version`, returning whether it was
    /// new (i.e. not previously recorded). The config is persisted whenever a new pair is added;
    /// write errors are ignored so a read-only config location doesn't disrupt the debugger.
    pub fn mark_event_seen(&mut self, version: &str, phase: i8, event: i32) -> bool {
        let is_new = self
            .seen_events
            .entry(version.to_string())
            .or_default()
            .insert((phase, event));
        if is_new {
            let _ = self.save();
        }
        is_new
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_through_toml() {
        let mut config = Config::default();
        config.mark_event_seen("SLPS-20178", 0, 1);
        config.mark_event_seen("SLPS-20178", 1, 5);
        config.mark_event_seen("SLPM-74405", 0, 1);

        let text = toml::to_string_pretty(&config).unwrap();
        let parsed: Config = toml::from_str(&text).unwrap();

        assert_eq!(parsed.version, CONFIG_VERSION);
        assert_eq!(parsed.seen_events, config.seen_events);
    }

    #[test]
    fn mark_event_seen_reports_new_only_once() {
        let mut config = Config::default();
        assert!(config.mark_event_seen("SLPS-20178", 2, 3));
        assert!(!config.mark_event_seen("SLPS-20178", 2, 3));
        // same pair, different version is still new
        assert!(config.mark_event_seen("SLPM-74405", 2, 3));
    }

    #[test]
    fn missing_fields_use_defaults() {
        let config: Config = toml::from_str("").unwrap();
        assert_eq!(config.version, CONFIG_VERSION);
        assert!(config.seen_events.is_empty());
    }
}
