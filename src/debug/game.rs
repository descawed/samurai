use binrw::binrw;
use bytemuck::Zeroable;
use sysinfo::Pid;

use super::{DebugError, Result};
use super::emulator::Emulator;

const FINGERPRINT_STRING: &[u8] = b"CreateFormatString: arg is not string.";
const GAME_STATE_SIZE: usize = 0x568;
/// Number of unique characters in the game
const NUM_CHARACTERS: usize = 103;
/// Maximum number of characters that can be in any given event at the same time
const MAX_EVENT_CHARACTERS: u32 = 30;
const CHARACTER_DATA_SIZE: usize = 0x200;
const CHARACTER_SIZE: usize = 0xcd0;
// size of both the list head and a list entry
const LINKED_LIST_SIZE: usize = 12;

#[binrw]
#[derive(Debug, Clone, Zeroable)]
pub struct GameState {
    pub gp: i32,
    unk004: [u8; 0x7c],
    pub status: i8, // 2 = SetGameStop, 3 = SetGameClear, 4 = ???
    pub map_id: i8,
    unk_map_id: i8,
    pub exit_id: i8,
    pub map_time_id: i8,
    unk_map_time_id: i8,
    pub phase_id: i8,
    pub player_footing: i8,
    pub event_man_flags: [i8; 128],
    pub event_pro_flags: [i8; 32],
    pub player_money: i16,
    unk12a: i16,
    pub player_num_kills: i32,
    pub difficulty: i32,
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
    pub chara_id: i32,
    pub health: i16,
    pub max_health: i16,
    pub weapon_id: i16,
    pub samurai_value: i16,
    pub battle_value: i16,
    is_dead: i8,
    friend_flag: i8,
    footing: i8,
    unk065: i8,
    pub daikon_flag: i8,
    death_item: i8,
    pub level: i8,
    unk069: i8,
    unk06a: i8,
    unk06b: i8,
    unk06c: i32,
    unk070: i32,
    possible_weapons: [i16; 100],
    unk13c: [u8; 0xc4],
}

impl CharacterData {
    const fn const_default() -> Self {
        Self {
            transform: [0.0; 16],
            unk040: [0.0; 4],
            chara_type_id: 0,
            chara_id: 0,
            health: 0,
            max_health: 0,
            weapon_id: 0,
            samurai_value: 0,
            battle_value: 0,
            is_dead: 0,
            friend_flag: 0,
            footing: 0,
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
    weapon_id: i16,
    durability: i16,
    hardness: i16,
    health_bonus: i16,
    attack: i16,
    defense: i16,
}

impl Default for WeaponInstance {
    fn default() -> Self {
        Self::zeroed()
    }
}

#[binrw]
#[derive(Debug, Clone, Zeroable)]
pub struct CharacterLine {
    line_range: f32,
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
    timeout_seconds: u32,
}

impl Default for CharacterTimeout {
    fn default() -> Self {
        Self::zeroed()
    }
}

#[binrw]
#[derive(Debug, Clone, Zeroable)]
pub struct Character {
    unk000: [u8; 0x350], // 000
    position: [f32; 4], // 350
    unk360: [u8; 0x28], // 360
    data: u32, // pointer to CharacterData; 388
    unk38c: [u8; 0x36], // 38c
    flags: u16, // 0x4 = invincible, 0x20 = pos fix mode; 3c2
    animation_id: i32, // ID in the low 12 bits, flags in the high bits; 3c4
    flags2: u32, // 0x2 = stop, 0x400 = has target character, 0x40000 = dead, 0x4000000 = hi face mode; 3c8
    unk3cc: u32, // 3cc
    base_max_health: i32, // 3d0
    unk3d4: [u8; 0x13c], // 3d4
    current_func_id: u32, // 510
    last_func_id: u32, // 514
    unk518: [u8; 0x20], // 518
    base_health: i16, // 538
    unk53a: [u8; 10], // 53a
    held_object: i32, // 544
    target_character: u32, // 548
    unk54c: u32, // 54c
    attacker: u32, // 550
    unk554: [u8; 12], // 554
    facing_character: u32, // 560
    unk564: [u8; 0x10], // 564
    weapons: [WeaponInstance; 3], // 574
    equipped_weapon_index: i16, // 5a4
    num_weapons: i16, // 5a6
    unk5a8: [u8; 0x38], // 5a8
    lines: [CharacterLine; 4], // 5e0
    line_view_fov_half: f32, // 790
    line_view_range: f32, // 794
    line_view_vertical_range: f32, // 798
    has_char_joined_view: [i8; NUM_CHARACTERS + 1], // 79c
    unk804: [u8; 0xc], // 804
    watched_chara_range: f32, // 810
    watched_chara_id: i32, // 814
    watch_type: i32, // 818
    unk81c: u32, // 81c
    watched_chara_start_position: [f32; 4], // 820
    is_drop_watch: i32, // 830
    watched_obj_id: i32, // 834
    unk838: [u8; 8], // 838
    say_task_id: i32, // 840
    unk844: [u8; 8], // 844
    say_duration: i16, // 84c
    say_start_delay: i16, // 84e
    listener_chara_id: i32, // 850
    unk854: [u8; 0xc], // 854
    timeouts: [CharacterTimeout; NUM_CHARACTERS], // 860
    flags3: u64, // b98
    event_modes: u64, // flags, 1 << EVENT constant; ba0
    unk_event_modes: u64, // ba8
    unkbb0: u32, // bb0
    ai_group_id: i32, // bb4
    unkbb8: [u8; 8], // bb8
    throw_count: i32, // bc0
    name: [u8; 16], // bc4
    unkbd4: u8, // bd4
    say_dead_flag: i8, // bd5
    unkbd6: [u8; 0x1e], // bd6
    ai_mode: i32, // bf4
    unkbf8: [u8; 0xa0], // bf8
    special_state: i32, // 1 = death blow, 2 = waiting; c98
    unkc9c: [u8; 0x34], // c9c
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
}

impl GameVersion {
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
    },
    GameVersion {
        name: "SLPM-74405",
        fingerprint_address: 0x00219ed0,
        game_state_address: 0x008ecd00,
        character_data_address: 0x00c175b0,
        character_list_address: 0x008dba3c,
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

    pub fn update(&mut self) -> Result<()> {
        // first, verify the emulator is still running the same game version
        if !self.version.matches(&self.emulator)? {
            // if not, see if we're running a different known version
            match GameVersion::search_for_version(&self.emulator)? {
                Some(version) => self.version = version,
                None => return Err(DebugError::GameLost),
            }
        }

        self.game_state = self.emulator.read(self.version.game_state_address, GAME_STATE_SIZE)?;
        self.character_data = self.emulator.read(self.version.character_data_address, CHARACTER_DATA_SIZE * NUM_CHARACTERS)?;

        let char_data_start = self.version.character_data_address as u32;
        let char_data_end = (self.version.character_data_address + CHARACTER_DATA_SIZE * NUM_CHARACTERS) as u32;

        // characters in the scene are a linked list. we need to be a bit careful here as we can't
        // read it all in one go, so it can change while we're reading it.
        self.characters.clear();

        let list_head: LinkedListHead = self.emulator.read(self.version.character_list_address, LINKED_LIST_SIZE)?;
        let list_begin = list_head.first as usize;
        if list_head.count == 0 || list_head.count > MAX_EVENT_CHARACTERS || !Emulator::is_address_valid(list_begin, LINKED_LIST_SIZE) {
            // if something looks fishy, it could mean things aren't initialized properly. we'll just bail.
            // on the other hand, if the count is 0, we simply don't need to do anything.
            return Ok(());
        }

        let list_end = self.version.character_list_address as u32;
        let mut entry: LinkedListEntry = self.emulator.read(list_begin, LINKED_LIST_SIZE)?;
        for _ in 0..list_head.count {
            let char_address = entry.object as usize;
            if !Emulator::is_address_valid(char_address, CHARACTER_SIZE) {
                break;
            }

            let character: Character = self.emulator.read(char_address, CHARACTER_SIZE)?;
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

    pub fn iter_characters(&self) -> impl Iterator<Item = &Character> {
        self.characters.iter()
    }
}