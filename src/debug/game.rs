use binrw::binrw;
use bytemuck::Zeroable;
use sysinfo::Pid;

use super::{DebugError, Result};
use super::constants::*;
use super::emulator::Emulator;

const FINGERPRINT_STRING: &[u8] = b"CreateFormatString: arg is not string.";
const GAME_STATE_SIZE: usize = 0x568;
/// Number of unique characters in the game
const NUM_CHARACTERS: usize = 103;
/// Maximum number of characters that can be in any given event at the same time
const MAX_EVENT_CHARACTERS: u32 = 30;
const CHARACTER_DATA_SIZE: usize = 0x200;
/// Size of a `Character` in the original release. Later versions insert an extra 0x100-byte block
/// (`unk860`) before `timeouts`, so a larger `character_size` indicates that block is present.
const CHARACTER_BASE_SIZE: usize = 0xcd0;
// size of both the list head and a list entry
const LINKED_LIST_SIZE: usize = 12;

#[binrw]
#[derive(Debug, Clone, Zeroable)]
pub struct GameState {
    pub gp: i32,
    unk004: [u8; 0x7c],
    pub status: i8, // 2 = SetGameStop, 3 = SetGameClear, 4 = ???
    pub map_id: Map,
    unk_map_id: Map,
    pub exit_id: i8,
    pub map_time_id: Time,
    unk_map_time_id: Time,
    pub phase_id: i8,
    pub player_footing: Footing,
    pub event_man_flags: [i8; 128],
    pub event_pro_flags: [EventProgress; 32],
    pub player_money: i16,
    unk12a: i16,
    pub player_num_kills: i32,
    pub difficulty: Difficulty,
    pub event_id: i32,
    pub int_vars: [i32; 256],
    pub event_act_end_flags: [i8; 32],
    player_name: [u8; 16],
}

impl Default for GameState {
    fn default() -> Self {
        Self::zeroed()
    }
}

#[binrw]
#[derive(Debug, Clone, Zeroable)]
pub struct CharacterData {
    pub transform: [f32; 16],
    unk040: [f32; 4],
    pub chara_type_id: i32,
    pub chara_id: CharacterId,
    pub health: i16,
    pub max_health: i16,
    pub weapon_id: i16,
    pub samurai_value: i16,
    pub battle_value: i16,
    is_dead: i8,
    pub friend_flag: Friend,
    pub footing: Footing,
    unk065: i8,
    pub daikon_flag: i8,
    death_item: i8,
    pub level: i8,
    unk069: i8,
    unk06a: i8,
    unk06b: i8,
    unk06c: i32,
    unk070: i32,
    pub possible_weapons: [i16; 100],
    unk13c: [u8; 0xc4],
}

impl CharacterData {
    const fn const_default() -> Self {
        Self {
            transform: [0.0; 16],
            unk040: [0.0; 4],
            chara_type_id: 0,
            chara_id: CharacterId::new(0),
            health: 0,
            max_health: 0,
            weapon_id: 0,
            samurai_value: 0,
            battle_value: 0,
            is_dead: 0,
            friend_flag: Friend::new(0),
            footing: Footing::new(0),
            unk065: 0,
            daikon_flag: 0,
            death_item: 0,
            level: 0,
            unk069: 0,
            unk06a: 0,
            unk06b: 0,
            unk06c: 0,
            unk070: 0,
            possible_weapons: [0; 100],
            unk13c: [0; 0xc4],
        }
    }

    pub const fn is_dead(&self) -> bool {
        self.is_dead != 0
    }

    pub fn death_item(&self) -> ObjectId {
        ObjectId::from(self.death_item as i32)
    }
}

impl Default for CharacterData {
    fn default() -> Self {
        Self::zeroed()
    }
}

#[binrw]
#[derive(Debug, Clone)]
struct LinkedListHead {
    last: u32,
    first: u32,
    count: u32,
}

#[binrw]
#[derive(Debug, Clone)]
struct LinkedListEntry {
    prev: u32,
    next: u32,
    object: u32,
}

#[binrw]
#[derive(Debug, Clone, Zeroable)]
pub struct WeaponInstance {
    unk00: i32,
    pub weapon_id: i16,
    pub durability: i16,
    pub hardness: i16,
    pub health_bonus: i16,
    pub attack: i16,
    pub defense: i16,
}

impl Default for WeaponInstance {
    fn default() -> Self {
        Self::zeroed()
    }
}

#[binrw]
#[derive(Debug, Clone, Zeroable)]
pub struct CharacterLine {
    pub line_range: f32,
    has_char_joined: [i8; NUM_CHARACTERS + 1],
}

impl Default for CharacterLine {
    fn default() -> Self {
        Self::zeroed()
    }
}

#[binrw]
#[derive(Debug, Clone, Zeroable)]
pub struct CharacterTimeout {
    is_enabled: i32,
    pub timeout_seconds: u32,
}

impl Default for CharacterTimeout {
    fn default() -> Self {
        Self::zeroed()
    }
}

#[binrw]
#[brw(import(has_extra: bool))]
#[derive(Debug, Clone, Zeroable)]
pub struct Character {
    unk000: [u8; 0x350], // 000
    pub position: [f32; 4], // 350
    unk360: [u8; 0x28], // 360
    data: u32, // pointer to CharacterData; 388
    unk38c: [u8; 0x36], // 38c
    flags: u16, // 0x4 = invincible, 0x20 = pos fix mode; 3c2
    pub animation_id: Animation, // ID in the low 12 bits, flags in the high bits; 3c4
    flags2: u32, // 0x2 = stop, 0x400 = has target character, 0x40000 = dead, 0x4000000 = hi face mode; 3c8
    unk3cc: u32, // 3cc
    pub base_max_health: i32, // 3d0
    unk3d4: [u8; 0x13c], // 3d4
    pub current_func_id: u32, // 510
    pub last_func_id: u32, // 514
    unk518: [u8; 0x20], // 518
    pub base_health: i16, // 538
    unk53a: [u8; 10], // 53a
    held_object: u32, // 544
    target_character: u32, // 548
    unk54c: u32, // 54c
    attacker: u32, // 550
    unk554: [u8; 12], // 554
    facing_character: u32, // 560
    unk564: [u8; 0x10], // 564
    pub weapons: [WeaponInstance; 3], // 574
    pub equipped_weapon_index: i16, // 5a4
    pub num_weapons: i16, // 5a6
    unk5a8: [u8; 0x38], // 5a8
    pub lines: [CharacterLine; 4], // 5e0
    pub line_view_fov_half: f32, // 790
    pub line_view_range: f32, // 794
    pub line_view_vertical_range: f32, // 798
    has_char_joined_view: [i8; NUM_CHARACTERS + 1], // 79c
    unk804: [u8; 0xc], // 804
    pub watched_chara_range: f32, // 810
    pub watched_chara_id: CharacterId, // 814
    pub watch_type: Watch, // 818
    unk81c: u32, // 81c
    pub watched_chara_start_position: [f32; 4], // 820
    is_drop_watch: i32, // 830
    pub watched_obj_id: ObjectId, // 834
    unk838: [u8; 8], // 838
    pub say_task_id: i32, // 840
    unk844: [u8; 8], // 844
    pub say_duration: i16, // 84c
    pub say_start_delay: i16, // 84e
    pub listener_chara_id: CharacterId, // 850
    unk854: [u8; 0xc], // 854
    // only present in the larger version (e.g. SLPM-74405); shifts everything below by 0x100
    #[br(if(has_extra, [0u8; 0x100]))]
    #[bw(if(has_extra))]
    unk860: [u8; 0x100], // 860
    pub timeouts: [CharacterTimeout; NUM_CHARACTERS], // 860 / 960 when unk860 present
    flags3: u64, // 0x20 = watch enabled; b98 / c98
    pub event_modes: u64, // flags, 1 << EVENT constant; ba0 / ca0
    unk_event_modes: u64, // ba8 / ca8
    unkbb0: u32, // bb0 / cb0
    pub ai_group_id: i32, // bb4 / cb4
    unkbb8: [u8; 8], // bb8 / cb8
    pub throw_count: i32, // bc0 / cc0
    name: [u8; 16], // bc4 / cc4
    unkbd4: u8, // bd4 / cd4
    say_dead_flag: i8, // bd5 / cd5
    unkbd6: [u8; 0x1e], // bd6 / cd6
    pub ai_mode: AiStatus, // bf4 / cf4
    unkbf8: [u8; 0xa0], // bf8 / cf8
    pub special_state: i32, // 1 = death blow, 2 = waiting; c98 / ca8
    unkc9c: [u8; 0x34], // c9c / cac
}

impl Character {
    pub const fn is_invincible(&self) -> bool {
        self.flags & 0x4 != 0
    }

    pub const fn is_pos_fix_mode(&self) -> bool {
        self.flags & 0x20 != 0
    }

    pub const fn is_stopped(&self) -> bool {
        self.flags2 & 0x2 != 0
    }

    pub const fn has_target_character(&self) -> bool {
        self.flags2 & 0x400 != 0
    }

    pub const fn is_dead(&self) -> bool {
        self.flags2 & 0x40000 != 0
    }

    pub const fn is_hi_face_mode(&self) -> bool {
        self.flags2 & 0x4000000 != 0
    }
    
    pub const fn is_watch_enabled(&self) -> bool {
        self.flags3 & 0x20 != 0
    }

    pub const fn say_dead_flag(&self) -> bool {
        self.say_dead_flag != 0
    }

    pub const fn is_drop_watch(&self) -> bool {
        self.is_drop_watch != 0
    }

    /// For each `EVENT_` mode, returns its name and whether the corresponding bit is set in
    /// `event_modes`. Entries are ordered by the constants' values.
    pub fn event_mode_flags(&self) -> [(&'static str, bool); 15] {
        event_modes(self.event_modes)
    }
}

impl Default for Character {
    fn default() -> Self {
        Self::zeroed()
    }
}

#[derive(Debug, Clone)]
pub struct GameVersion {
    name: &'static str,
    fingerprint_address: usize,
    game_state_address: usize,
    character_data_address: usize,
    character_list_address: usize,
    character_size: usize,
}

impl GameVersion {
    /// Whether this version includes the extra `unk860` block in `Character`.
    const fn character_has_extra(&self) -> bool {
        self.character_size > CHARACTER_BASE_SIZE
    }

    pub fn matches(&self, emulator: &Emulator) -> Result<bool> {
        let fingerprint_size = FINGERPRINT_STRING.len();
        let fingerprint_data = emulator.read_memory(self.fingerprint_address, fingerprint_size)?;
        Ok(fingerprint_data == FINGERPRINT_STRING)
    }

    pub fn search_for_version(emulator: &Emulator) -> Result<Option<&'static Self>> {
        for version in &GAME_VERSIONS {
            if version.matches(emulator)? {
                return Ok(Some(version));
            }
        }
        Ok(None)
    }
}

const GAME_VERSIONS: [GameVersion; 2] = [
    GameVersion {
        name: "SLPS-20178",
        fingerprint_address: 0x00213260,
        game_state_address: 0x008c6f00,
        character_data_address: 0x00bf13e0,
        character_list_address: 0x008b5c40,
        character_size: 0xcd0,
    },
    GameVersion {
        name: "SLPM-74405",
        fingerprint_address: 0x00219ed0,
        game_state_address: 0x008ecd00,
        character_data_address: 0x00c175b0,
        character_list_address: 0x008dba3c,
        character_size: 0xdd0,
    },
];

pub struct Game {
    version: &'static GameVersion,
    emulator: Emulator,
    pub game_state: GameState,
    pub character_data: [CharacterData; NUM_CHARACTERS],
    characters: Vec<Character>,
}

impl Game {
    pub fn new(version: &'static GameVersion, emulator: Emulator) -> Self {
        Self {
            version,
            emulator,
            game_state: GameState::default(),
            character_data: [const { CharacterData::const_default() }; NUM_CHARACTERS],
            characters: Vec::new(),
        }
    }

    pub fn detach(self) -> Emulator {
        self.emulator
    }

    pub fn pid(&self) -> Pid {
        self.emulator.pid()
    }

    pub fn version_name(&self) -> &'static str {
        self.version.name
    }

    pub fn update(&mut self) -> Result<()> {
        // first, verify the emulator is still running the same game version
        if !self.version.matches(&self.emulator)? {
            // if not, see if we're running a different known version
            match GameVersion::search_for_version(&self.emulator)? {
                Some(version) => self.version = version,
                None => return Err(DebugError::GameLost),
            }
        }

        self.game_state = self
            .emulator
            .read(self.version.game_state_address, GAME_STATE_SIZE)?;
        self.character_data = self.emulator.read(
            self.version.character_data_address,
            CHARACTER_DATA_SIZE * NUM_CHARACTERS,
        )?;

        let char_data_start = self.version.character_data_address as u32;
        let char_data_end =
            (self.version.character_data_address + CHARACTER_DATA_SIZE * NUM_CHARACTERS) as u32;

        // characters in the scene are a linked list. we need to be a bit careful here as we can't
        // read it all in one go, so it can change while we're reading it.
        self.characters.clear();

        let list_head: LinkedListHead = self
            .emulator
            .read(self.version.character_list_address, LINKED_LIST_SIZE)?;
        let list_begin = list_head.first as usize;
        if list_head.count == 0
            || list_head.count > MAX_EVENT_CHARACTERS
            || !Emulator::is_address_valid(list_begin, LINKED_LIST_SIZE)
        {
            // if something looks fishy, it could mean things aren't initialized properly. we'll just bail.
            // on the other hand, if the count is 0, we simply don't need to do anything.
            return Ok(());
        }

        let list_end = self.version.character_list_address as u32;
        let character_size = self.version.character_size;
        let has_extra = self.version.character_has_extra();
        let mut entry: LinkedListEntry = self.emulator.read(list_begin, LINKED_LIST_SIZE)?;
        for _ in 0..list_head.count {
            let char_address = entry.object as usize;
            if !Emulator::is_address_valid(char_address, character_size) {
                break;
            }

            let character: Character =
                self.emulator
                    .read_args(char_address, character_size, (has_extra,))?;
            // sanity check: the character's data pointer should be in the range of the character data
            if character.data < char_data_start || character.data >= char_data_end {
                break;
            }
            self.characters.push(character);

            // if we encounter the list end pointer, stop even if we haven't found the reported number of characters
            if entry.next == list_end {
                break;
            }

            let next_address = entry.next as usize;
            if !Emulator::is_address_valid(next_address, LINKED_LIST_SIZE) {
                break;
            }
            entry = self.emulator.read(next_address, LINKED_LIST_SIZE)?;
        }

        Ok(())
    }

    pub fn iter_characters(&self) -> impl Iterator<Item = (&Character, &CharacterData)> {
        self.characters.iter().map(|chara| {
            // we know the data pointer is in the character data range because we checked it in update()
            let data_index = (chara.data as usize - self.version.character_data_address) / CHARACTER_DATA_SIZE;
            (chara, &self.character_data[data_index])
        })
    }
}
