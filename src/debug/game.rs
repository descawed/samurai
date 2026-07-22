use std::io::Cursor;

use binrw::{BinRead, BinReaderExt, binrw};
use bytemuck::Zeroable;
use sysinfo::Pid;

use super::{DebugError, Result};
use super::constants::*;
use super::emulator::{Console, Emulator};
use super::layout::{
    self, CharacterLayout, CharacterMenuLayout, EngineLayout, MainMenuLayout, VersionLayout,
};

const FINGERPRINT_STRING: &[u8] = b"CreateFormatString: arg is not string.";
const GAME_STATE_BASE_SIZE: usize = 0x568;
/// Number of unique characters in the game
const NUM_CHARACTERS: usize = 103;
/// Maximum number of characters that can be in any given event at the same time
const MAX_EVENT_CHARACTERS: u32 = 30;
const CHARACTER_DATA_SIZE: usize = 0x200;
// size of both the list head and a list entry
const LINKED_LIST_SIZE: usize = 12;
/// MIPS assembly: jr $ra; nop;
const JR_RA_NOP: [u8; 8] = [8, 0, 0xE0, 3, 0, 0, 0, 0];
/// Size of the [`Camera`] struct in memory.
const CAMERA_SIZE: usize = 0xc0;
/// Offset of the position vector within the [`Camera`] struct. The position, look, and up vectors
/// are contiguous from here; this 48-byte region is all free cam writes back, leaving the camera's
/// other fields (e.g. its target character) untouched.
const CAMERA_TRANSFORM_OFFSET: usize = 0x90;
/// World up axis. y is the vertical axis; positive is up.
const WORLD_UP: [f32; 3] = [0.0, 1.0, 0.0];

/// Decode a single field of type `T` from `buf` at `offset`. Field types and offsets are static,
/// so a failure here means a layout table disagrees with its declared size — surfaced as a parse
/// error rather than a panic since `buf` ultimately comes from live emulator memory.
fn field<T>(buf: &[u8], offset: usize) -> Result<T>
where
    for<'a> T: BinRead<Args<'a> = ()>,
{
    // an out-of-range offset yields an empty slice, which binrw reports as an EOF parse error
    let mut cursor = Cursor::new(buf.get(offset..).unwrap_or_default());
    Ok(cursor.read_le()?)
}

/// Decode a flags field that is a u64 on PS2 (`wide`) but a u32 on PSP. The bit assignments are
/// version-independent, so the narrow form widens losslessly.
fn flags_field(buf: &[u8], offset: usize, wide: bool) -> Result<u64> {
    if wide {
        field(buf, offset)
    } else {
        field::<u32>(buf, offset).map(u64::from)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum EngineMode {
    Booting,
    InGame,
    Loading,
    BattleMode,
    SaveCheckpoint,
    PhaseChange,
    MainMenu,
    Unknown(i32),
}

/// The engine's global state object. Only the fields the debugger uses are modeled; see
/// [`EngineLayout`] for where they live in each version.
#[derive(Debug, Clone, Zeroable)]
pub struct Engine {
    mode: i32,
    /// Counts frames since the game started. Runs all the time except during boot, movie playback,
    /// and ending slides.
    pub frame_counter: u32,
    /// Pointer to the player's `Character`, when one is loaded.
    pub player: u32,
}

impl Engine {
    fn read(buf: &[u8], layout: &EngineLayout) -> Result<Self> {
        Ok(Self {
            mode: field(buf, layout.mode)?,
            frame_counter: field(buf, layout.frame_counter)?,
            player: field(buf, layout.player)?,
        })
    }

    pub const fn mode(&self) -> EngineMode {
        match self.mode {
            0 => EngineMode::Booting,
            1 => EngineMode::InGame,
            2 => EngineMode::Loading,
            3 => EngineMode::BattleMode,
            4 => EngineMode::SaveCheckpoint,
            5 => EngineMode::PhaseChange,
            7 => EngineMode::MainMenu,
            _ => EngineMode::Unknown(self.mode),
        }
    }
}

impl Default for Engine {
    fn default() -> Self {
        Self::zeroed()
    }
}

#[binrw]
#[derive(Debug, Clone, Zeroable)]
pub struct Camera {
    target_character: u32,
    unk004: [u8; 0x8c],
    position: [f32; 4],
    look_vector: [f32; 4],
    up_vector: [f32; 4],
}

impl Default for Camera {
    fn default() -> Self {
        Self::zeroed()
    }
}

/// The xyz components of a homogeneous `[f32; 4]` vector, ignoring w.
fn xyz(v: [f32; 4]) -> [f32; 3] {
    [v[0], v[1], v[2]]
}

/// Overwrite the xyz components of `v`, preserving its w component.
fn set_xyz(v: &mut [f32; 4], xyz: [f32; 3]) {
    v[0] = xyz[0];
    v[1] = xyz[1];
    v[2] = xyz[2];
}

fn normalize3(v: [f32; 3]) -> [f32; 3] {
    let len = (v[0] * v[0] + v[1] * v[1] + v[2] * v[2]).sqrt();
    if len > 0.0 {
        [v[0] / len, v[1] / len, v[2] / len]
    } else {
        v
    }
}

fn cross3(a: [f32; 3], b: [f32; 3]) -> [f32; 3] {
    [
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    ]
}

/// Rotate `v` about the (not necessarily unit-length) `axis` by `angle` radians, via Rodrigues'
/// rotation formula.
fn rotate3(v: [f32; 3], axis: [f32; 3], angle: f32) -> [f32; 3] {
    let (sin, cos) = angle.sin_cos();
    let k = normalize3(axis);
    let cross = cross3(k, v);
    let dot = k[0] * v[0] + k[1] * v[1] + k[2] * v[2];
    [
        v[0] * cos + cross[0] * sin + k[0] * dot * (1.0 - cos),
        v[1] * cos + cross[1] * sin + k[1] * dot * (1.0 - cos),
        v[2] * cos + cross[2] * sin + k[2] * dot * (1.0 - cos),
    ]
}

/// Active free-camera state. Holds the working copy of the [`Camera`] that gets written back to
/// emulator memory each frame, the resolved address of the live camera, and the original
/// instructions we patched over so they can be restored when free cam is turned off.
///
/// Motion is expressed in camera-relative terms (dolly/strafe/rise, yaw/pitch) so callers don't
/// have to do any vector math; the geometry lives here and is independent of the emulator.
#[derive(Debug, Clone)]
pub struct FreeCam {
    camera: Camera,
    camera_address: usize,
    saved_instructions: [u8; 8],
}

impl FreeCam {
    /// Normalized direction the camera is looking.
    fn forward(&self) -> [f32; 3] {
        normalize3(xyz(self.camera.look_vector))
    }

    /// Normalized camera-right axis (look × world-up).
    fn right(&self) -> [f32; 3] {
        normalize3(cross3(self.forward(), WORLD_UP))
    }

    fn translate(&mut self, dir: [f32; 3], dist: f32) {
        // zip stops at dir's length (3), leaving the position's w component untouched
        for (pos, d) in self.camera.position.iter_mut().zip(dir) {
            *pos += d * dist;
        }
    }

    /// Move forward (positive) or backward (negative) along the look vector.
    pub fn dolly(&mut self, dist: f32) {
        let forward = self.forward();
        self.translate(forward, dist);
    }

    /// Move right (positive) or left (negative), perpendicular to the look vector.
    pub fn strafe(&mut self, dist: f32) {
        let right = self.right();
        self.translate(right, dist);
    }

    /// Move up (positive) or down (negative) along the world vertical axis.
    pub fn rise(&mut self, dist: f32) {
        self.translate(WORLD_UP, dist);
    }

    /// Turn the camera left/right about the world vertical axis. The entire orientation (both look
    /// and up vectors) is rotated, so panning stays purely horizontal regardless of the current
    /// pitch.
    pub fn yaw(&mut self, radians: f32) {
        let look = rotate3(xyz(self.camera.look_vector), WORLD_UP, radians);
        set_xyz(&mut self.camera.look_vector, look);
        let up = rotate3(xyz(self.camera.up_vector), WORLD_UP, radians);
        set_xyz(&mut self.camera.up_vector, up);
    }

    /// Rotate the look direction up/down about the camera-right axis, keeping the up vector
    /// consistent.
    pub fn pitch(&mut self, radians: f32) {
        let right = self.right();
        let look = rotate3(xyz(self.camera.look_vector), right, radians);
        set_xyz(&mut self.camera.look_vector, look);
        set_xyz(&mut self.camera.up_vector, normalize3(cross3(right, look)));
    }

    pub fn position(&self) -> [f32; 3] {
        xyz(self.camera.position)
    }

    pub fn look(&self) -> [f32; 3] {
        xyz(self.camera.look_vector)
    }
}

/// A main-menu mode, decoded from the version-specific numbering (see the mode tables in
/// [`layout`]). Not every variant exists in every version: `LoadPlayer2Save` and `TutorialMenu`
/// are PS2-only, `VsLobby` is PSP-only, and `SpecialMoviesMenu` doesn't exist in the original
/// release.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum MenuMode {
    LoadSaveData(i32),
    TrailerMovie,
    TitleMenu,
    TutorialMenu,
    OptionsMenu,
    RecordMenu,
    OverwriteSaveData,
    NewGameCharacterMenu,
    LoadPlayer2Save,
    /// The PSP's two-screen ad-hoc VS-mode lobby.
    VsLobby(i32),
    BattleModeMenu,
    ResultsScreen(i32),
    SaveGame,
    ContinueFromSave,
    SpecialMoviesMenu,
    /// A transition code briefly visible as the menu mode while a menu hands off to gameplay
    /// (new game, battle mode, or the teacher intro).
    StartingGame(i32),
    Unknown(i32),
}

#[derive(Debug, Clone)]
pub struct MainMenu {
    menu_mode: MenuMode,
    // Pointer to the new-game character menu. This heads a block of sub-menu pointers (battle
    // mode, options, save data, results, title, record, ...) whose order varies by version; add
    // fields here and to [`MainMenuLayout`] as they become useful.
    new_game_character_menu: u32,
}

impl MainMenu {
    fn read(buf: &[u8], layout: &MainMenuLayout) -> Result<Self> {
        // the raw menu mode is the first field in every version
        Ok(Self {
            menu_mode: (layout.menu_mode)(field(buf, 0)?),
            new_game_character_menu: field(buf, layout.new_game_character_menu)?,
        })
    }

    pub const fn menu_mode(&self) -> MenuMode {
        self.menu_mode
    }
}

impl Default for MainMenu {
    fn default() -> Self {
        Self {
            menu_mode: MenuMode::Unknown(-1),
            new_game_character_menu: 0,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum CharacterMenuMode {
    Inactive,
    CharacterSettings,
    NameEntry,
    WeaponSelect,
    StartNewGame,
    Unknown(u32),
}

impl CharacterMenuMode {
    const fn from_raw(value: u32) -> Self {
        match value {
            0 => Self::Inactive,
            1 => Self::CharacterSettings,
            2 => Self::NameEntry,
            3 => Self::WeaponSelect,
            4 => Self::StartNewGame,
            _ => Self::Unknown(value),
        }
    }
}

/// The hidden player model selected in the character-creation menu. On PS2 the game only tracks
/// whether the Manji name cheat is active; the PSP replaced that with a mode covering its three
/// chord-unlocked secret models.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum SecretPlayerModel {
    None,
    Manji,
    Suzu, // Suzu replaces Manji on the PSP version
    Teacher,
    Robot,
    Unknown(i32),
}

#[derive(Debug, Clone)]
pub struct NewGameCharacterMenu {
    active_mode: u32,
    /// 0 = Name Entry, 1 = Head Select, 2 = Body Select, 3 = Weapon Select
    pub selected_section: u32,
    next_mode: u32,
    pub player_model_index: i32,
    secret_model: SecretPlayerModel,
}

impl NewGameCharacterMenu {
    fn read(buf: &[u8], layout: &CharacterMenuLayout) -> Result<Self> {
        Ok(Self {
            // the mode/section header sits at the same offsets in every version
            active_mode: field(buf, 0x8)?,
            selected_section: field(buf, 0xc)?,
            next_mode: field(buf, 0x10)?,
            player_model_index: field(buf, layout.player_model_index)?,
            secret_model: (layout.decode_secret_model)(field(buf, layout.secret_model)?),
        })
    }

    pub const fn active_mode(&self) -> CharacterMenuMode {
        CharacterMenuMode::from_raw(self.active_mode)
    }

    pub const fn next_mode(&self) -> CharacterMenuMode {
        CharacterMenuMode::from_raw(self.next_mode)
    }

    pub const fn secret_model(&self) -> SecretPlayerModel {
        self.secret_model
    }

    pub const fn is_manji(&self) -> bool {
        matches!(self.secret_model, SecretPlayerModel::Manji)
    }
}

impl Default for NewGameCharacterMenu {
    fn default() -> Self {
        Self {
            active_mode: 0,
            selected_section: 0,
            next_mode: 0,
            player_model_index: 0,
            secret_model: SecretPlayerModel::None,
        }
    }
}

#[binrw]
#[brw(import(has_extra: bool))]
#[derive(Debug, Clone, Zeroable)]
pub struct GameState {
    pub gp: i32,
    #[br(if(has_extra, [0u8; 0x7c]))]
    #[bw(if(has_extra))]
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

/// An in-scene character. This is the debugger's logical model; per-version field locations live
/// in [`CharacterLayout`].
#[derive(Debug, Clone)]
pub struct Character {
    pub position: [f32; 4],
    // pointer to this character's CharacterData
    data: u32,
    flags: u16, // 0x4 = invincible, 0x20 = pos fix mode
    /// ID in the low 12 bits, flags in the high bits
    pub animation_id: Animation,
    flags2: u32, // 0x2 = stop, 0x4 = blocking, 0x400 = has target character, 0x40000 = dead, 0x4000000 = hi face mode
    pub base_max_health: i32,
    pub current_command_id: Command,
    pub last_command_id: Command,
    pub base_health: i16,
    /// Pointer to the object the character is holding, if any.
    pub held_object: u32,
    /// Pointer to the [`Character`] this character is targeting, if any.
    pub target_character: u32,
    /// Pointer to the [`Character`] that last attacked this character, if any.
    pub attacker: u32,
    /// Pointer to the [`Character`] this character is facing, if any.
    pub facing_character: u32,
    pub weapons: [WeaponInstance; 3],
    pub equipped_weapon_index: i16,
    pub num_weapons: i16,
    pub lines: [CharacterLine; 4],
    pub line_view_fov_half: f32,
    pub line_view_range: f32,
    pub line_view_vertical_range: f32,
    /// Per-character flags for whether each character has entered this character's view (indexed
    /// by `CHID_`).
    pub has_char_joined_view: [i8; NUM_CHARACTERS + 1],
    pub watched_chara_range: f32,
    pub watched_chara_id: CharacterId,
    pub watch_type: Watch,
    pub watched_chara_start_position: [f32; 4],
    is_drop_watch: i32,
    pub watched_obj_id: ObjectId,
    pub say_task_id: i32,
    pub say_duration: i16,
    pub say_start_delay: i16,
    pub listener_chara_id: CharacterId,
    pub timeouts: [CharacterTimeout; NUM_CHARACTERS],
    flags3: u64, // 0x20 = watch enabled
    /// flags, 1 << EVENT constant
    pub event_modes: u64,
    pub ai_group_id: i32,
    pub throw_count: i32,
    /// The character's name as raw bytes in the game's custom text encoding.
    pub name: [u8; 16],
    say_dead_flag: i8,
    pub ai_mode: AiStatus,
    pub ai_command: Command,
    /// 1 = death blow, 2 = waiting
    pub special_state: i32,
}

impl Character {
    fn read(buf: &[u8], layout: &CharacterLayout) -> Result<Self> {
        Ok(Self {
            position: field(buf, layout.position)?,
            data: field(buf, layout.data)?,
            flags: field(buf, layout.flags)?,
            animation_id: field(buf, layout.animation_id)?,
            flags2: field(buf, layout.flags2)?,
            base_max_health: field(buf, layout.base_max_health)?,
            current_command_id: field(buf, layout.current_command_id)?,
            last_command_id: field(buf, layout.last_command_id)?,
            base_health: field(buf, layout.base_health)?,
            held_object: field(buf, layout.held_object)?,
            target_character: field(buf, layout.target_character)?,
            attacker: field(buf, layout.attacker)?,
            facing_character: field(buf, layout.facing_character)?,
            weapons: field(buf, layout.weapons)?,
            equipped_weapon_index: field(buf, layout.equipped_weapon_index)?,
            num_weapons: field(buf, layout.num_weapons)?,
            lines: field(buf, layout.lines)?,
            line_view_fov_half: field(buf, layout.line_view_fov_half)?,
            line_view_range: field(buf, layout.line_view_range)?,
            line_view_vertical_range: field(buf, layout.line_view_vertical_range)?,
            has_char_joined_view: field(buf, layout.has_char_joined_view)?,
            watched_chara_range: field(buf, layout.watched_chara_range)?,
            watched_chara_id: field(buf, layout.watched_chara_id)?,
            watch_type: field(buf, layout.watch_type)?,
            watched_chara_start_position: field(buf, layout.watched_chara_start_position)?,
            is_drop_watch: field(buf, layout.is_drop_watch)?,
            watched_obj_id: field(buf, layout.watched_obj_id)?,
            say_task_id: field(buf, layout.say_task_id)?,
            say_duration: field(buf, layout.say_duration)?,
            say_start_delay: field(buf, layout.say_start_delay)?,
            listener_chara_id: if layout.byte_listener {
                CharacterId::new(field::<i8>(buf, layout.listener_chara_id)?.into())
            } else {
                field(buf, layout.listener_chara_id)?
            },
            timeouts: field(buf, layout.timeouts)?,
            flags3: flags_field(buf, layout.flags3, layout.wide_flags)?,
            event_modes: flags_field(buf, layout.event_modes, layout.wide_flags)?,
            ai_group_id: field(buf, layout.ai_group_id)?,
            throw_count: field(buf, layout.throw_count)?,
            name: field(buf, layout.name)?,
            say_dead_flag: field(buf, layout.say_dead_flag)?,
            ai_mode: field(buf, layout.ai_mode)?,
            ai_command: field(buf, layout.ai_command)?,
            special_state: field(buf, layout.special_state)?,
        })
    }

    pub const fn is_invincible(&self) -> bool {
        self.flags & 0x4 != 0
    }

    pub const fn is_pos_fix_mode(&self) -> bool {
        self.flags & 0x20 != 0
    }

    pub const fn is_stopped(&self) -> bool {
        self.flags2 & 0x2 != 0
    }

    pub const fn is_blocking(&self) -> bool {
        self.flags2 & 0x4 != 0
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

#[derive(Debug, Clone)]
pub struct GameVersion {
    name: &'static str,
    console: Console,
    fingerprint_address: usize,
    game_state_address: usize,
    character_data_address: usize,
    engine_address: usize,
    camera_target_character_address: usize,
    free_cam_patch_address: usize,
    /// Offset within the engine of the pointer to the [`Camera`].
    camera_pointer_offset: usize,
    game_state_size: usize,
    has_hard_difficulty: bool,
    /// Physical layouts of the structures whose shape varies by version.
    layout: &'static VersionLayout,
}

impl GameVersion {
    const fn game_state_has_extra(&self) -> bool {
        self.game_state_size >= GAME_STATE_BASE_SIZE
    }

    const fn supports_free_cam(&self) -> bool {
        self.camera_target_character_address != 0
    }

    const fn main_menu_address(&self) -> usize {
        self.engine_address + self.layout.engine.main_menu_pointer
    }

    /// Address of the pointer to the [`Camera`] within the engine.
    const fn camera_pointer_address(&self) -> usize {
        self.engine_address + self.camera_pointer_offset
    }

    /// Address of the character [`LinkedListHead`] embedded in the engine. This address also
    /// doubles as the sentinel marking the end of the list.
    const fn character_list_head_address(&self) -> usize {
        self.engine_address + self.layout.engine.character_list
    }

    pub fn matches(&self, emulator: &Emulator) -> Result<bool> {
        let fingerprint_size = FINGERPRINT_STRING.len();
        let fingerprint_data = emulator.read_memory(self.fingerprint_address, fingerprint_size)?;
        Ok(fingerprint_data == FINGERPRINT_STRING)
    }

    pub fn search_for_version(emulator: &Emulator) -> Result<Option<&'static Self>> {
        for version in &GAME_VERSIONS {
            if version.console == emulator.console() && version.matches(emulator)? {
                return Ok(Some(version));
            }
        }
        Ok(None)
    }
}

static GAME_VERSIONS: [GameVersion; 3] = [
    GameVersion {
        name: "SLPS-20178",
        console: Console::Ps2,
        fingerprint_address: 0x00213260,
        game_state_address: 0x008c6f00,
        character_data_address: 0x00bf13e0,
        engine_address: 0x008b5c00,
        camera_target_character_address: 0x00225170,
        free_cam_patch_address: 0x0011d370,
        camera_pointer_offset: 0x3c,
        game_state_size: GAME_STATE_BASE_SIZE,
        has_hard_difficulty: false,
        layout: &layout::JP,
    },
    GameVersion {
        name: "SLPM-74405",
        console: Console::Ps2,
        fingerprint_address: 0x00219ed0,
        game_state_address: 0x008ecd00,
        character_data_address: 0x00c175b0,
        engine_address: 0x008dba00,
        camera_target_character_address: 0x0022aef0,
        free_cam_patch_address: 0x0011d120,
        camera_pointer_offset: 0x38,
        game_state_size: GAME_STATE_BASE_SIZE,
        has_hard_difficulty: true,
        layout: &layout::KANZENBAN,
    },
    GameVersion {
        name: "ULJS-00155",
        console: Console::Psp,
        fingerprint_address: 0x0894e528,
        game_state_address: 0x08d54b90,
        character_data_address: 0x08d7dd10,
        engine_address: 0x08d43900,
        // free cam isn't supported on PSP yet; the camera hasn't been mapped
        camera_target_character_address: 0,
        free_cam_patch_address: 0,
        camera_pointer_offset: 0,
        game_state_size: 0x4ec,
        has_hard_difficulty: true,
        layout: &layout::PSP,
    },
];

pub struct Game {
    version: &'static GameVersion,
    /// Always `Some` while the game is live. It is `take`n by [`detach`](Self::detach), and held in
    /// an `Option` so [`Game`] can implement [`Drop`] (which would otherwise forbid moving the
    /// emulator out) to restore any free-cam patch when the game goes away.
    emulator: Option<Emulator>,
    pub engine: Engine,
    main_menu: MainMenu,
    new_game_character_menu: NewGameCharacterMenu,
    pub game_state: GameState,
    pub character_data: [CharacterData; NUM_CHARACTERS],
    /// In-scene characters paired with their addresses in emulator memory.
    characters: Vec<(u32, Character)>,
    /// Present while free camera mode is active.
    free_cam: Option<FreeCam>,
}

impl Game {
    pub fn new(version: &'static GameVersion, emulator: Emulator) -> Self {
        Self {
            version,
            emulator: Some(emulator),
            engine: Engine::default(),
            main_menu: MainMenu::default(),
            new_game_character_menu: NewGameCharacterMenu::default(),
            game_state: GameState::default(),
            character_data: [const { CharacterData::const_default() }; NUM_CHARACTERS],
            characters: Vec::new(),
            free_cam: None,
        }
    }

    /// Borrow the emulator. Panics only if called after [`detach`](Self::detach), which never
    /// happens since `detach` consumes `self`.
    fn emulator(&self) -> &Emulator {
        self.emulator.as_ref().expect("emulator already detached")
    }

    pub fn detach(mut self) -> Emulator {
        // restore any free-cam patch before we give up our handle to the emulator
        let _ = self.disable_free_cam();
        self.emulator.take().expect("emulator already detached")
    }

    pub fn pid(&self) -> Pid {
        self.emulator().pid()
    }

    pub fn emulator_name(&self) -> &'static str {
        self.emulator().name()
    }

    pub fn version_name(&self) -> &'static str {
        self.version.name
    }

    pub fn difficulty_name(&self) -> &'static str {
        if self.version.has_hard_difficulty {
            match self.game_state.difficulty {
                0 => "Easy",
                1 => "Normal",
                2 => "Hard",
                _ => "Unknown",
            }
        } else {
            match self.game_state.difficulty {
                0 => "Normal",
                1 => "Easy",
                _ => "Unknown",
            }
        }
    }

    fn read_main_menu(&mut self) -> Result<()> {
        let layout = self.version.layout;
        let main_menu_ptr: u32 = self.emulator().read(self.version.main_menu_address(), 4)?;
        let buf = self
            .emulator()
            .read_memory(main_menu_ptr as usize, layout.main_menu.size)?;
        self.main_menu = MainMenu::read(&buf, &layout.main_menu)?;
        if self.main_menu.menu_mode() == MenuMode::NewGameCharacterMenu {
            let buf = self.emulator().read_memory(
                self.main_menu.new_game_character_menu as usize,
                layout.character_menu.size,
            )?;
            self.new_game_character_menu =
                NewGameCharacterMenu::read(&buf, &layout.character_menu)?;
        }
        Ok(())
    }

    pub fn update(&mut self) -> Result<()> {
        self.update_with(false)
    }

    /// Update the cached game state. When `skip_characters` is set, the (large) character data
    /// table and the in-scene character list are not read, which saves a significant amount of time
    /// for consumers that only care about engine, menu, and game state (e.g. the autosplitter).
    pub fn update_with(&mut self, skip_characters: bool) -> Result<()> {
        // first, verify the emulator is still running the same game version
        if !self.version.matches(self.emulator())? {
            // if not, see if we're running a different known version
            match GameVersion::search_for_version(self.emulator())? {
                Some(version) => self.version = version,
                None => return Err(DebugError::GameLost),
            }
        }

        let engine_buf = self
            .emulator()
            .read_memory(self.version.engine_address, self.version.layout.engine.size)?;
        self.engine = Engine::read(&engine_buf, &self.version.layout.engine)?;

        // while free cam is active, keep overwriting the camera with our controlled transform.
        // best-effort: if the camera pointer has gone stale (e.g. a scene change), don't tear the
        // whole debugger down over it.
        if self.free_cam.is_some() {
            let _ = self.write_free_cam();
        }

        self.game_state = self
            .emulator()
            .read_args(
                self.version.game_state_address,
                self.version.game_state_size,
                (self.version.game_state_has_extra(),),
            )?;

        if skip_characters {
            // the autosplitter still needs menu data, but never touches character data
            self.characters.clear();
            if self.engine.mode() == EngineMode::MainMenu {
                self.read_main_menu()?;
            }
            return Ok(());
        }

        self.character_data = self.emulator().read(
            self.version.character_data_address,
            CHARACTER_DATA_SIZE * NUM_CHARACTERS,
        )?;

        match self.engine.mode() {
            EngineMode::MainMenu => {
                self.characters.clear();
                self.read_main_menu()?;
            }
            // battle mode does not use the same character list as in-game; need to figure out
            // where those characters are stored
            EngineMode::InGame => {
                let char_data_start = self.version.character_data_address as u32;
                let char_data_end =
                    (self.version.character_data_address + CHARACTER_DATA_SIZE * NUM_CHARACTERS) as u32;

                // characters in the scene are a linked list. we need to be a bit careful here as we can't
                // read it all in one go, so it can change while we're reading it.
                self.characters.clear();

                let head_address = self.version.character_list_head_address();
                let list_head: LinkedListHead =
                    self.emulator().read(head_address, LINKED_LIST_SIZE)?;
                let list_begin = list_head.first as usize;
                if list_head.count == 0
                    || list_head.count > MAX_EVENT_CHARACTERS
                    || !self.emulator().is_address_valid(list_begin, LINKED_LIST_SIZE)
                {
                    // if something looks fishy, it could mean things aren't initialized properly. we'll just bail.
                    // on the other hand, if the count is 0, we simply don't need to do anything.
                    return Ok(());
                }

                let list_end = head_address as u32;
                let character_layout = &self.version.layout.character;
                let mut entry: LinkedListEntry = self.emulator().read(list_begin, LINKED_LIST_SIZE)?;
                for _ in 0..list_head.count {
                    let char_address = entry.object as usize;
                    if !self.emulator().is_address_valid(char_address, character_layout.size) {
                        break;
                    }

                    let buf = self
                        .emulator()
                        .read_memory(char_address, character_layout.size)?;
                    let character = Character::read(&buf, character_layout)?;
                    // sanity check: the character's data pointer should be in the range of the character data
                    if character.data < char_data_start || character.data >= char_data_end {
                        break;
                    }
                    self.characters.push((entry.object, character));

                    // if we encounter the list end pointer, stop even if we haven't found the reported number of characters
                    if entry.next == list_end {
                        break;
                    }

                    let next_address = entry.next as usize;
                    if !self.emulator().is_address_valid(next_address, LINKED_LIST_SIZE) {
                        break;
                    }
                    entry = self.emulator().read(next_address, LINKED_LIST_SIZE)?;
                }
            }
            _ => self.characters.clear(),
        }

        Ok(())
    }

    /// Read a single character's [`CharacterData`] directly from emulator memory, identified by its
    /// index (a `CHID_` value) in the character data array. Unlike [`update_with`](Self::update_with),
    /// this reads just the one record on demand, which is useful for consumers running with
    /// `skip_characters` that still need a specific character (e.g. the autosplitter watching the
    /// final boss's health).
    pub fn read_character_data(&self, id: usize) -> Result<CharacterData> {
        let address = self.version.character_data_address + id * CHARACTER_DATA_SIZE;
        self.emulator().read(address, CHARACTER_DATA_SIZE)
    }

    /// Read the character ID (`CHID_` index) of the character the camera is currently targeting.
    /// Returns `None` if the camera target pointer doesn't currently point to a valid character.
    /// Like [`read_character_data`](Self::read_character_data), this reads directly from emulator
    /// memory on demand, so it works even when character data is skipped on update.
    pub fn camera_target_character_id(&self) -> Result<Option<usize>> {
        let emulator = self.emulator();
        let data_pointer_offset = self.version.layout.character.data;
        let target =
            emulator.read::<u32>(self.version.camera_target_character_address, 4)? as usize;
        if !emulator.is_address_valid(target, data_pointer_offset + 4) {
            return Ok(None);
        }

        // identify the character by which CharacterData record its data pointer refers to
        let data = emulator.read::<u32>(target + data_pointer_offset, 4)? as usize;
        let offset = match data.checked_sub(self.version.character_data_address) {
            Some(offset) if offset % CHARACTER_DATA_SIZE == 0 => offset,
            _ => return Ok(None),
        };

        let index = offset / CHARACTER_DATA_SIZE;
        Ok((index < NUM_CHARACTERS).then_some(index))
    }

    /// Iterate over the in-scene characters as (address in emulator memory, character, character data).
    pub fn iter_characters(&self) -> impl Iterator<Item = (u32, &Character, &CharacterData)> {
        self.characters.iter().map(|&(address, ref chara)| {
            // we know the data pointer is in the character data range because we checked it in update()
            let data_index = (chara.data as usize - self.version.character_data_address) / CHARACTER_DATA_SIZE;
            (address, chara, &self.character_data[data_index])
        })
    }

    pub fn main_menu(&self) -> Option<&MainMenu> {
        (self.engine.mode() == EngineMode::MainMenu).then(|| &self.main_menu)
    }

    pub fn new_game_character_menu(&self) -> Option<&NewGameCharacterMenu> {
        (self.engine.mode() == EngineMode::MainMenu && self.main_menu.menu_mode() == MenuMode::NewGameCharacterMenu).then(|| &self.new_game_character_menu)
    }
    
    pub const fn supports_free_cam(&self) -> bool {
        self.version.supports_free_cam()
    }

    /// Whether free camera mode is currently active.
    pub fn is_free_cam(&self) -> bool {
        self.free_cam.is_some()
    }

    /// The active free camera, if any. Use [`adjust_free_cam`](Self::adjust_free_cam) to move it.
    pub fn free_cam(&self) -> Option<&FreeCam> {
        self.free_cam.as_ref()
    }

    /// Toggle free camera mode, returning the new state (`true` if now active). Turning it on
    /// patches out the game's camera update and snapshots the live camera; turning it off restores
    /// the original instructions.
    pub fn toggle_free_cam(&mut self) -> Result<bool> {
        if self.free_cam.is_some() {
            self.disable_free_cam()?;
            Ok(false)
        } else if self.version.supports_free_cam() {
            self.enable_free_cam()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn enable_free_cam(&mut self) -> Result<()> {
        let emulator = self.emulator();
        let patch_address = self.version.free_cam_patch_address;
        // save the original instructions before patching so we can restore them later
        let saved_instructions: [u8; 8] = emulator.read(patch_address, JR_RA_NOP.len())?;
        // resolve and snapshot the live camera
        let camera_address = emulator.read::<u32>(self.version.camera_pointer_address(), 4)? as usize;
        let camera: Camera = emulator.read(camera_address, CAMERA_SIZE)?;
        // patch out the game's camera update so it stops fighting us
        emulator.write_memory(patch_address, &JR_RA_NOP)?;
        self.free_cam = Some(FreeCam {
            camera,
            camera_address,
            saved_instructions,
        });
        Ok(())
    }

    fn disable_free_cam(&mut self) -> Result<()> {
        if let Some(free_cam) = self.free_cam.take()
            && let Some(emulator) = self.emulator.as_ref()
        {
            emulator.write_memory(self.version.free_cam_patch_address, &free_cam.saved_instructions)?;
        }
        Ok(())
    }

    /// Write the working camera transform (position/look/up only) back to emulator memory.
    fn write_free_cam(&self) -> Result<()> {
        if let Some(free_cam) = self.free_cam.as_ref() {
            Self::write_camera_transform(self.emulator(), free_cam)?;
        }
        Ok(())
    }

    fn write_camera_transform(emulator: &Emulator, free_cam: &FreeCam) -> Result<()> {
        let base = free_cam.camera_address + CAMERA_TRANSFORM_OFFSET;
        emulator.write(base, &free_cam.camera.position)?;
        emulator.write(base + 0x10, &free_cam.camera.look_vector)?;
        emulator.write(base + 0x20, &free_cam.camera.up_vector)?;
        Ok(())
    }

    /// Apply an adjustment to the active free camera and immediately write it back, so motion is
    /// responsive rather than waiting for the next [`update`](Self::update). No-op if free cam is
    /// off.
    pub fn adjust_free_cam(&mut self, f: impl FnOnce(&mut FreeCam)) -> Result<()> {
        // disjoint field borrows: `free_cam` mutably, `emulator` immutably
        if let Some(free_cam) = self.free_cam.as_mut()
            && let Some(emulator) = self.emulator.as_ref()
        {
            f(free_cam);
            Self::write_camera_transform(emulator, free_cam)?;
        }
        Ok(())
    }
}

impl Drop for Game {
    fn drop(&mut self) {
        // restore the camera patch if free cam is still on, so we don't leave the game frozen when
        // the debugger exits or the game is lost. best-effort: nothing useful to do on failure.
        let _ = self.disable_free_cam();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Write little-endian `bytes` into `buf` at `offset`.
    fn put(buf: &mut [u8], offset: usize, bytes: &[u8]) {
        buf[offset..offset + bytes.len()].copy_from_slice(bytes);
    }

    /// Every layout's fields must decode from within its declared size; a field at or crossing
    /// the end of a zeroed buffer of `size` bytes fails with an EOF parse error.
    #[test]
    fn layouts_fit_declared_sizes() {
        for version in [&layout::JP, &layout::KANZENBAN, &layout::PSP] {
            Engine::read(&vec![0; version.engine.size], &version.engine)
                .expect("zeroed engine should decode");
            MainMenu::read(&vec![0; version.main_menu.size], &version.main_menu)
                .expect("zeroed main menu should decode");
            NewGameCharacterMenu::read(
                &vec![0; version.character_menu.size],
                &version.character_menu,
            )
            .expect("zeroed character menu should decode");
            Character::read(&vec![0; version.character.size], &version.character)
                .expect("zeroed character should decode");
        }
    }

    #[test]
    fn ps2_character_fields_decode_from_their_offsets() {
        // kanzenban; jp differs only in the 0x100 shift of the fields from timeouts on
        let layout = &layout::KANZENBAN.character;
        let mut buf = vec![0; layout.size];
        put(&mut buf, 0x350, &42.0f32.to_le_bytes()); // position.x
        put(&mut buf, 0x3c8, &0x40000u32.to_le_bytes()); // flags2: dead
        put(&mut buf, 0x538, &0x1234u16.to_le_bytes()); // base_health
        put(&mut buf, 0x850, &9i32.to_le_bytes()); // listener_chara_id (i32 on PS2)
        put(&mut buf, 0xc98, &0x20u64.to_le_bytes()); // flags3 (u64 on PS2): watch enabled
        put(&mut buf, 0xca0, &0x120u64.to_le_bytes()); // event_modes
        put(&mut buf, 0xd98, &1i32.to_le_bytes()); // special_state

        let chara = Character::read(&buf, layout).unwrap();
        assert_eq!(chara.position[0], 42.0);
        assert!(chara.is_dead());
        assert_eq!(chara.base_health, 0x1234);
        assert_eq!(chara.listener_chara_id.value(), 9);
        assert!(chara.is_watch_enabled());
        assert_eq!(chara.event_modes, 0x120);
        assert_eq!(chara.special_state, 1);
    }

    #[test]
    fn psp_character_fields_decode_from_their_moved_offsets() {
        let layout = &layout::PSP.character;
        let mut buf = vec![0; layout.size];
        put(&mut buf, 0x4d0, &42.0f32.to_le_bytes()); // position.x
        put(&mut buf, 0x53c, &0x40000u32.to_le_bytes()); // flags2: dead
        put(&mut buf, 0x6a8, &0x1234u16.to_le_bytes()); // base_health
        put(&mut buf, 0x9c0, &[7]); // listener_chara_id (a single byte on PSP)
        put(&mut buf, 0xe08, &0x20u32.to_le_bytes()); // flags3 (u32 on PSP): watch enabled
        put(&mut buf, 0xe0c, &0x120u32.to_le_bytes()); // event_modes
        put(&mut buf, 0xef8, &1i32.to_le_bytes()); // special_state

        let chara = Character::read(&buf, layout).unwrap();
        assert_eq!(chara.position[0], 42.0);
        assert!(chara.is_dead());
        assert_eq!(chara.base_health, 0x1234);
        assert_eq!(chara.listener_chara_id.value(), 7);
        assert!(chara.is_watch_enabled());
        assert_eq!(chara.event_modes, 0x120);
        assert_eq!(chara.special_state, 1);
    }

    #[test]
    fn psp_engine_fields_decode_from_their_moved_offsets() {
        let layout = &layout::PSP.engine;
        let mut buf = vec![0; layout.size];
        put(&mut buf, 0x28, &7i32.to_le_bytes()); // mode: MainMenu
        put(&mut buf, 0x5c, &1000u32.to_le_bytes()); // frame_counter

        let engine = Engine::read(&buf, layout).unwrap();
        assert_eq!(engine.mode(), EngineMode::MainMenu);
        assert_eq!(engine.frame_counter, 1000);
    }

    /// A free camera at the origin looking down +z with +y up.
    fn test_free_cam() -> FreeCam {
        let mut camera = Camera::default();
        camera.position = [0.0, 0.0, 0.0, 1.0];
        camera.look_vector = [0.0, 0.0, 1.0, 0.0];
        camera.up_vector = [0.0, 1.0, 0.0, 0.0];
        FreeCam {
            camera,
            camera_address: 0,
            saved_instructions: [0; 8],
        }
    }

    fn assert_close(actual: [f32; 3], expected: [f32; 3]) {
        for (a, e) in actual.iter().zip(expected) {
            assert!((a - e).abs() < 1e-5, "got {actual:?}, expected {expected:?}");
        }
    }

    #[test]
    fn dolly_moves_along_look() {
        let mut cam = test_free_cam();
        cam.dolly(2.0);
        assert_close(cam.position(), [0.0, 0.0, 2.0]);
        // w component must be preserved
        assert_eq!(cam.camera.position[3], 1.0);
    }

    #[test]
    fn rise_moves_along_world_up() {
        let mut cam = test_free_cam();
        cam.rise(3.0);
        assert_close(cam.position(), [0.0, 3.0, 0.0]);
    }

    #[test]
    fn strafe_moves_perpendicular_to_look() {
        let mut cam = test_free_cam();
        cam.strafe(1.0);
        // right = look × world-up = (0,0,1) × (0,1,0) = (-1, 0, 0)
        assert_close(cam.position(), [-1.0, 0.0, 0.0]);
    }

    #[test]
    fn yaw_rotates_look_about_world_up() {
        let mut cam = test_free_cam();
        cam.yaw(std::f32::consts::FRAC_PI_2);
        assert_close(cam.look(), [1.0, 0.0, 0.0]);
    }

    #[test]
    fn pitch_rotates_look_and_keeps_up_consistent() {
        let mut cam = test_free_cam();
        cam.pitch(std::f32::consts::FRAC_PI_2);
        // looking straight up, with up now pointing back along -z
        assert_close(cam.look(), [0.0, 1.0, 0.0]);
        assert_close(xyz(cam.camera.up_vector), [0.0, 0.0, -1.0]);
    }

    #[test]
    fn yaw_pan_stays_horizontal_when_pitched() {
        let mut cam = test_free_cam();
        // pitch down 45°, then pan; the look vector's vertical component must not change
        cam.pitch(-std::f32::consts::FRAC_PI_4);
        let pitched_y = cam.look()[1];
        cam.yaw(0.7);
        assert!((cam.look()[1] - pitched_y).abs() < 1e-5);
        // the basis stays orthonormal: up remains perpendicular to look
        let look = cam.look();
        let up = xyz(cam.camera.up_vector);
        let dot = look[0] * up[0] + look[1] * up[1] + look[2] * up[2];
        assert!(dot.abs() < 1e-5, "look and up should stay orthogonal, dot = {dot}");
    }
}
