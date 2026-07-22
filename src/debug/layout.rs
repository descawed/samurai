//! Physical memory layouts of the version-divergent game structures.
//!
//! The structs in [`game`](super::game) are the debugger's logical model: *what* we read. The
//! tables here describe *where* each field lives in a particular version's memory. The two PS2
//! versions differ only slightly (kanzenban inserts an extra 0x100-byte block into `Character`
//! and shifts the engine's embedded character list head down to 0x3c), but the PSP release
//! reshuffled everything: fields moved, the 64-bit flag fields narrowed to 32 bits, the menu
//! pointer block was reordered, and the menu mode numbering changed. Encoding the differences as
//! data keeps the readers version-agnostic; supporting another layout means writing another table,
//! not another parser.

use super::game::{MenuMode, SecretPlayerModel};

#[derive(Debug)]
pub(crate) struct EngineLayout {
    /// How many bytes to read from the engine address to cover every field below.
    pub size: usize,
    pub mode: usize,
    pub frame_counter: usize,
    pub player: usize,
    /// Offset of the in-scene character `LinkedListHead` embedded in the engine. Every version
    /// embeds the head (its address doubles as the end-of-list sentinel); only the offset moves.
    /// The head is read fresh from memory when walking the list, not from the engine snapshot, so
    /// `size` need not cover it.
    pub character_list: usize,
    /// Offset from the engine base of the pointer to the live `MainMenu`.
    pub main_menu_pointer: usize,
}

#[derive(Debug)]
pub(crate) struct MainMenuLayout {
    /// Allocated size of the `MainMenu` object.
    pub size: usize,
    /// Offset of the pointer to the new-game character menu. This is the head of a block of
    /// sub-menu pointers whose order varies by version; only the ones the debugger uses get
    /// entries here.
    pub new_game_character_menu: usize,
    /// Decode this version's menu mode numbering (the raw value at offset 0).
    pub menu_mode: fn(i32) -> MenuMode,
}

#[derive(Debug)]
pub(crate) struct CharacterMenuLayout {
    /// Allocated size of the new-game character menu object.
    pub size: usize,
    pub player_model_index: usize,
    /// Offset of the secret-model field
    pub secret_model: usize,
    pub decode_secret_model: fn(i32) -> SecretPlayerModel,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct CharacterLayout {
    /// Allocated size of a `Character` object.
    pub size: usize,
    pub position: usize,
    /// Offset of the pointer to the character's `CharacterData` record.
    pub data: usize,
    pub flags: usize,
    pub animation_id: usize,
    pub flags2: usize,
    pub base_max_health: usize,
    pub current_command_id: usize,
    pub last_command_id: usize,
    pub base_health: usize,
    pub held_object: usize,
    pub target_character: usize,
    pub attacker: usize,
    pub facing_character: usize,
    pub weapons: usize,
    pub equipped_weapon_index: usize,
    pub num_weapons: usize,
    pub lines: usize,
    pub line_view_fov_half: usize,
    pub line_view_range: usize,
    pub line_view_vertical_range: usize,
    pub has_char_joined_view: usize,
    pub watched_chara_range: usize,
    pub watched_chara_id: usize,
    pub watch_type: usize,
    pub watched_chara_start_position: usize,
    pub is_drop_watch: usize,
    pub watched_obj_id: usize,
    pub say_task_id: usize,
    pub say_duration: usize,
    pub say_start_delay: usize,
    pub listener_chara_id: usize,
    pub timeouts: usize,
    pub flags3: usize,
    pub event_modes: usize,
    pub ai_group_id: usize,
    pub throw_count: usize,
    pub name: usize,
    pub say_dead_flag: usize,
    pub ai_mode: usize,
    pub ai_command: usize,
    pub special_state: usize,
    /// `flags3`/`event_modes` are u64 on PS2 but were narrowed to u32 in the 32-bit PSP build.
    /// The bit assignments are unchanged.
    pub wide_flags: bool,
    /// `listener_chara_id` is an i32 on PS2 but a single byte on PSP.
    pub byte_listener: bool,
}

/// The complete set of layouts for one game version.
#[derive(Debug)]
pub(crate) struct VersionLayout {
    pub engine: EngineLayout,
    pub main_menu: MainMenuLayout,
    pub character_menu: CharacterMenuLayout,
    pub character: CharacterLayout,
}

// Menu mode numbering. Modes 0-9 mean the same thing in every version. From 10 up:
// - jp: 10 LoadPlayer2Save, 11 BattleModeMenu, 12/13 ResultsScreen, 14 SaveGame,
//   15 ContinueFromSave. When a mode's handler starts a game it sets the menu mode to a
//   transition code (new game, new game via model cheat, battle mode, teacher intro) that the
//   menu loop consumes; those codes sit just past the last real mode, so they briefly show up as
//   menu modes 16-19.
// - kanzenban: appends SpecialMoviesMenu at 16, pushing the start codes to 17-20.
// - psp: the tutorial menu is gone (its mode 5 handler is a no-op) and the two-screen ad-hoc VS
//   lobby takes 10/11 in place of LoadPlayer2Save, shifting the rest: 12 BattleModeMenu,
//   13/14 ResultsScreen, 15 SaveGame, 16 ContinueFromSave, 17 SpecialMoviesMenu, start codes
//   18-21.
fn menu_mode_common(raw: i32) -> Option<MenuMode> {
    Some(match raw {
        0..=2 => MenuMode::LoadSaveData(raw),
        3 => MenuMode::TrailerMovie,
        4 => MenuMode::TitleMenu,
        5 => MenuMode::TutorialMenu,
        6 => MenuMode::OptionsMenu,
        7 => MenuMode::RecordMenu,
        8 => MenuMode::OverwriteSaveData,
        9 => MenuMode::NewGameCharacterMenu,
        _ => return None,
    })
}

fn menu_mode_jp(raw: i32) -> MenuMode {
    menu_mode_common(raw).unwrap_or(match raw {
        10 => MenuMode::LoadPlayer2Save,
        11 => MenuMode::BattleModeMenu,
        12 | 13 => MenuMode::ResultsScreen(raw),
        14 => MenuMode::SaveGame,
        15 => MenuMode::ContinueFromSave,
        16..=19 => MenuMode::StartingGame(raw),
        _ => MenuMode::Unknown(raw),
    })
}

fn menu_mode_kanzenban(raw: i32) -> MenuMode {
    menu_mode_common(raw).unwrap_or(match raw {
        10 => MenuMode::LoadPlayer2Save,
        11 => MenuMode::BattleModeMenu,
        12 | 13 => MenuMode::ResultsScreen(raw),
        14 => MenuMode::SaveGame,
        15 => MenuMode::ContinueFromSave,
        16 => MenuMode::SpecialMoviesMenu,
        17..=20 => MenuMode::StartingGame(raw),
        _ => MenuMode::Unknown(raw),
    })
}

fn menu_mode_psp(raw: i32) -> MenuMode {
    menu_mode_common(raw).unwrap_or(match raw {
        // 5 decodes as TutorialMenu above, but on PSP the mode is an unreachable no-op; it's
        // mapped anyway rather than special-cased since it can never come up
        10 | 11 => MenuMode::VsLobby(raw),
        12 => MenuMode::BattleModeMenu,
        13 | 14 => MenuMode::ResultsScreen(raw),
        15 => MenuMode::SaveGame,
        16 => MenuMode::ContinueFromSave,
        17 => MenuMode::SpecialMoviesMenu,
        18..=21 => MenuMode::StartingGame(raw),
        _ => MenuMode::Unknown(raw),
    })
}

fn secret_model_ps2(raw: i32) -> SecretPlayerModel {
    match raw {
        0 => SecretPlayerModel::None,
        1 => SecretPlayerModel::Manji,
        // the teacher was only turned into a secret model starting with the PAL version, but
        // earlier versions simply don't use a value of 2, so there shouldn't be any issues with
        // checking for it
        2 => SecretPlayerModel::Teacher,
        _ => SecretPlayerModel::Unknown(raw),
    }
}

// PSP replaced Manji with Suzu and turned the robot into a secret model since its normal slot was
// replaced by the WotS 3 protagonist
fn secret_model_psp(raw: i32) -> SecretPlayerModel {
    match raw {
        0 => SecretPlayerModel::None,
        1 => SecretPlayerModel::Suzu,
        2 => SecretPlayerModel::Teacher,
        3 => SecretPlayerModel::Robot,
        _ => SecretPlayerModel::Unknown(raw),
    }
}

const JP_CHARACTER: CharacterLayout = CharacterLayout {
    size: 0xcd0,
    position: 0x350,
    data: 0x388,
    flags: 0x3c2,
    animation_id: 0x3c4,
    flags2: 0x3c8,
    base_max_health: 0x3d0,
    current_command_id: 0x510,
    last_command_id: 0x514,
    base_health: 0x538,
    held_object: 0x544,
    target_character: 0x548,
    attacker: 0x550,
    facing_character: 0x560,
    weapons: 0x574,
    equipped_weapon_index: 0x5a4,
    num_weapons: 0x5a6,
    lines: 0x5e0,
    line_view_fov_half: 0x790,
    line_view_range: 0x794,
    line_view_vertical_range: 0x798,
    has_char_joined_view: 0x79c,
    watched_chara_range: 0x810,
    watched_chara_id: 0x814,
    watch_type: 0x818,
    watched_chara_start_position: 0x820,
    is_drop_watch: 0x830,
    watched_obj_id: 0x834,
    say_task_id: 0x840,
    say_duration: 0x84c,
    say_start_delay: 0x84e,
    listener_chara_id: 0x850,
    timeouts: 0x860,
    flags3: 0xb98,
    event_modes: 0xba0,
    ai_group_id: 0xbb4,
    throw_count: 0xbc0,
    name: 0xbc4,
    say_dead_flag: 0xbd5,
    ai_mode: 0xbf4,
    ai_command: 0xbf8,
    special_state: 0xc98,
    wide_flags: true,
    byte_listener: false,
};

// kanzenban inserts a 0x100-byte block just before `timeouts`; everything from there on shifts
// by 0x100.
const KANZENBAN_CHARACTER: CharacterLayout = CharacterLayout {
    size: 0xdd0,
    timeouts: 0x960,
    flags3: 0xc98,
    event_modes: 0xca0,
    ai_group_id: 0xcb4,
    throw_count: 0xcc0,
    name: 0xcc4,
    say_dead_flag: 0xcd5,
    ai_mode: 0xcf4,
    ai_command: 0xcf8,
    special_state: 0xd98,
    ..JP_CHARACTER
};

pub(crate) static JP: VersionLayout = VersionLayout {
    engine: EngineLayout {
        size: 0x44,
        mode: 0x0,
        frame_counter: 0x24,
        player: 0x28,
        character_list: 0x40,
        main_menu_pointer: 0x28980,
    },
    main_menu: MainMenuLayout {
        size: 0x68,
        new_game_character_menu: 0x48,
        menu_mode: menu_mode_jp,
    },
    character_menu: CharacterMenuLayout {
        size: 0x74,
        player_model_index: 0x50,
        secret_model: 0x6c,
        decode_secret_model: secret_model_ps2,
    },
    character: JP_CHARACTER,
};

pub(crate) static KANZENBAN: VersionLayout = VersionLayout {
    engine: EngineLayout {
        size: 0x40,
        mode: 0x0,
        frame_counter: 0x24,
        player: 0x28,
        character_list: 0x3c,
        main_menu_pointer: 0x28980,
    },
    main_menu: MainMenuLayout {
        // grown by the special-movies-menu pointer appended at 0x68
        size: 0x6c,
        new_game_character_menu: 0x48,
        menu_mode: menu_mode_kanzenban,
    },
    character_menu: CharacterMenuLayout {
        size: 0x74,
        player_model_index: 0x50,
        secret_model: 0x6c,
        decode_secret_model: secret_model_ps2,
    },
    character: KANZENBAN_CHARACTER,
};

// The PSP engine begins with an OS-specific prefix (kernel callback IDs, a thread record, a
// pointer to the render context), pushing the fields the debugger reads to new offsets. The
// character list is embedded jp-style rather than referenced kanzenban-style.
pub(crate) static PSP: VersionLayout = VersionLayout {
    engine: EngineLayout {
        size: 0x80,
        mode: 0x28,
        frame_counter: 0x5c,
        player: 0x60,
        character_list: 0x74,
        main_menu_pointer: 0x28600,
    },
    main_menu: MainMenuLayout {
        // same size as kanzenban: the VS-lobby pointer was added at 0x50 and the tutorial menu's
        // removed. The rest of the pointer block shifted, but the new-game character menu still
        // leads it.
        size: 0x6c,
        new_game_character_menu: 0x48,
        menu_mode: menu_mode_psp,
    },
    character_menu: CharacterMenuLayout {
        // two GP-derived grid-size fields were inserted, shifting everything from the model index
        // on by 8
        size: 0x7c,
        player_model_index: 0x58,
        secret_model: 0x74,
        decode_secret_model: secret_model_psp,
    },
    // The PSP Character reshuffle isn't a uniform shift: insertions of 0x180/0x174/0x170 land in
    // different bands, the trailing AI block sits at jp+0x260, and the u64 flag fields narrowed
    // to u32. Offsets verified against the PSP constructor chain and the per-field readers
    // (CharaTakeDamage, CheckEvents, AiInitCharaState, etc.).
    character: CharacterLayout {
        size: 0xf30,
        position: 0x4d0,
        data: 0x508,
        flags: 0x536,
        animation_id: 0x538,
        flags2: 0x53c,
        base_max_health: 0x544,
        current_command_id: 0x680,
        last_command_id: 0x684,
        base_health: 0x6a8,
        held_object: 0x6b4,
        target_character: 0x6b8,
        attacker: 0x6c0,
        facing_character: 0x6d0,
        weapons: 0x6e4,
        equipped_weapon_index: 0x714,
        num_weapons: 0x716,
        lines: 0x750,
        line_view_fov_half: 0x900,
        line_view_range: 0x904,
        line_view_vertical_range: 0x908,
        has_char_joined_view: 0x90c,
        watched_chara_range: 0x980,
        watched_chara_id: 0x984,
        watch_type: 0x988,
        watched_chara_start_position: 0x990,
        is_drop_watch: 0x9a0,
        watched_obj_id: 0x9a4,
        say_task_id: 0x9b0,
        say_duration: 0x9bc,
        say_start_delay: 0x9be,
        listener_chara_id: 0x9c0,
        timeouts: 0xad0,
        flags3: 0xe08,
        event_modes: 0xe0c,
        ai_group_id: 0xe18,
        throw_count: 0xe24,
        name: 0xe28,
        say_dead_flag: 0xe39,
        ai_mode: 0xe54,
        ai_command: 0xe58,
        special_state: 0xef8,
        wide_flags: false,
        byte_listener: true,
    },
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn menu_mode_numbering_shifts_by_version() {
        // modes 0-9 are the same everywhere
        for decode in [menu_mode_jp, menu_mode_kanzenban, menu_mode_psp] {
            assert_eq!(decode(0), MenuMode::LoadSaveData(0));
            assert_eq!(decode(9), MenuMode::NewGameCharacterMenu);
        }

        assert_eq!(menu_mode_jp(10), MenuMode::LoadPlayer2Save);
        assert_eq!(menu_mode_jp(11), MenuMode::BattleModeMenu);
        assert_eq!(menu_mode_jp(16), MenuMode::StartingGame(16));

        // kanzenban appends the special movies menu, pushing the start codes up by one
        assert_eq!(menu_mode_kanzenban(15), MenuMode::ContinueFromSave);
        assert_eq!(menu_mode_kanzenban(16), MenuMode::SpecialMoviesMenu);
        assert_eq!(menu_mode_kanzenban(17), MenuMode::StartingGame(17));

        // the PSP VS lobby takes two modes, shifting everything after it
        assert_eq!(menu_mode_psp(10), MenuMode::VsLobby(10));
        assert_eq!(menu_mode_psp(11), MenuMode::VsLobby(11));
        assert_eq!(menu_mode_psp(12), MenuMode::BattleModeMenu);
        assert_eq!(menu_mode_psp(14), MenuMode::ResultsScreen(14));
        assert_eq!(menu_mode_psp(16), MenuMode::ContinueFromSave);
        assert_eq!(menu_mode_psp(17), MenuMode::SpecialMoviesMenu);
        assert_eq!(menu_mode_psp(21), MenuMode::StartingGame(21));
        assert_eq!(menu_mode_psp(22), MenuMode::Unknown(22));
    }

    #[test]
    fn secret_model_decoding() {
        assert_eq!(secret_model_ps2(0), SecretPlayerModel::None);
        assert_eq!(secret_model_ps2(1), SecretPlayerModel::Manji);
        assert_eq!(secret_model_ps2(2), SecretPlayerModel::Teacher);
        assert_eq!(secret_model_psp(0), SecretPlayerModel::None);
        assert_eq!(secret_model_psp(1), SecretPlayerModel::Suzu);
        assert_eq!(secret_model_psp(2), SecretPlayerModel::Teacher);
        assert_eq!(secret_model_psp(3), SecretPlayerModel::Robot);
        assert_eq!(secret_model_psp(4), SecretPlayerModel::Unknown(4));
    }
}
