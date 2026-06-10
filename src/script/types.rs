use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::ops::Deref;
use std::rc::{Rc, Weak};
use std::str::FromStr;
use std::sync::LazyLock;

use anyhow::{Error, anyhow};
use common_macros::hash_map;
use strum::{EnumIter, EnumString};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, EnumString, EnumIter, Default)]
pub enum EnumType {
    #[strum(serialize = "MTAS")]
    Animation,
    #[strum(serialize = "CHID")]
    Character,
    #[strum(serialize = "SAY")]
    Say,
    #[strum(serialize = "COMMAND")]
    Command,
    #[strum(serialize = "PARAM_ATTACK")]
    ParamAttack,
    #[strum(serialize = "PARAM_WEAPON")]
    ParamWeapon,
    #[strum(serialize = "PARAM_KICK")]
    ParamKick,
    #[strum(serialize = "FEEL")]
    Feeling,
    #[strum(serialize = "EVENT")]
    Event,
    #[strum(serialize = "EFFECT")]
    Effect,
    #[strum(serialize = "CAMERA")]
    Camera,
    #[strum(serialize = "WATCH")]
    Watch,
    #[strum(serialize = "MAPID")]
    Map,
    #[strum(serialize = "TIME")]
    Time,
    #[strum(serialize = "DAMAGE")]
    Damage,
    #[strum(serialize = "AI")]
    Ai,
    #[strum(serialize = "OBJ")]
    Object,
    #[strum(serialize = "BGM")]
    Bgm,
    #[strum(serialize = "FRIEND")]
    Friend,
    #[strum(serialize = "EVENTPRO")]
    EventProgress,
    #[strum(serialize = "FOOTING")]
    Footing,
    #[strum(serialize = "BTN")]
    Button,
    #[strum(serialize = "OBJECT")]
    ObjectSet,
    // float-valued coordinate families (map-entry, map-exit, traffic, and forge positions)
    #[strum(serialize = "MAPIN")]
    MapIn,
    #[strum(serialize = "MAPOUT")]
    MapOut,
    #[strum(serialize = "TRAFFIC")]
    Traffic,
    #[strum(serialize = "SMITH")]
    Smith,
    // these don't follow the normal naming convention and need special handling
    Duration, // a float duration in seconds (e.g. for SetTimeAction); INIT_TIME is its sentinel
    Boolean,
    Relation,
    FadeDir,
    FadeType,
    Initialize,
    Null,
    #[default]
    Any, // any other type not identified above
    Conflict, // we've detected multiple conflicting types for this value and should treat it as an unknown type
}

impl EnumType {
    pub fn is_concrete(&self) -> bool {
        !matches!(self, Self::Any | Self::Conflict)
    }

    /// Whether this is one of the float-valued coordinate families. These are only restored in
    /// assignment/declaration contexts (where the developers routed them through named variables
    /// like `#MapX`/`#GoalX`); a bare float passed inline to a call or compared against is almost
    /// always a literal position, so restoring it there would produce spurious constants.
    pub fn is_coordinate(&self) -> bool {
        matches!(self, Self::MapIn | Self::MapOut | Self::Traffic | Self::Smith)
    }

    /// Choose the more specific of this type and another type
    ///
    /// If the level of specificity is the same, the other type is preferred.
    pub fn choose(&self, other: Self) -> Self {
        if *self == Self::Conflict || (self.is_concrete() && other.is_concrete() && *self != other)
        {
            Self::Conflict
        } else if other == Self::Any || (self.is_concrete() && !other.is_concrete()) {
            *self
        } else {
            other
        }
    }

    /// Replace this type with another type if the new type is not less specific than the old type
    pub fn update(&mut self, new_type: Self) -> Self {
        *self = self.choose(new_type);
        *self
    }

    pub fn get_constant_type(constant: &str) -> Option<Self> {
        match constant {
            "ON" | "OFF" => Some(Self::Boolean),
            // a float duration sentinel (distinct from the integer TIME_* time-of-day constants)
            "INIT_TIME" => Some(Self::Duration),
            "NO_RELATION" | "ENEMY_RELATION" | "FRIEND_RELATION" => Some(Self::Relation),
            "INIT" => Some(Self::Initialize),
            "NULL" => Some(Self::Null),
            "FADE_IN_INIT" | "FADE_IN" | "FADE_OUT" => Some(Self::FadeDir),
            "FADE_NORMAL" | "FADE_SPECIAL" => Some(Self::FadeType),
            "SAY_WEAPON_ON" | "SAY_WEAPON_OFF" => Some(Self::Command),
            _ => {
                let index = constant
                    .match_indices('_')
                    .find(|(_, s)| *s != "PARAM")? // PARAMs need the next part of the name as well
                    .0;
                let prefix = &constant[..index];
                Self::from_str(prefix).ok()
            }
        }
    }
}

/// How a built-in function argument's type is resolved. Most arguments are `Fixed`, but some
/// depend on the values of earlier arguments (`Switch`, `SwitchAfter`) or accept a generic
/// sentinel constant (`INIT`/`ON`/`OFF`) in place of their nominal type (`Sentinel`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ArgType {
    Fixed(EnumType),
    /// Nominal type, but for the listed argument values a generic sentinel constant takes priority
    /// over a type-specific constant of the same value: `-1` -> `INIT`, `0` -> `OFF`, `1` -> `ON`.
    /// (e.g. `SetCameraPos`'s `Camera` argument accepts `-1` as `INIT` rather than `CAMERA_INIT`,
    /// but still resolves `0`/`1` to the real `CAMERA_WORLD`/`CAMERA_CHAR`.)
    Sentinel { ty: EnumType, accept: &'static [i32] },
    /// Type chosen by the literal value of argument `on` (e.g. `SetCharAction` argument 2 selects
    /// the type of argument 3). Resolves to `Any` if argument `on` isn't a known literal.
    Switch {
        on: usize,
        cases: &'static [(i32, EnumType)],
        default: EnumType,
    },
    /// Stateful vararg: `base` until some preceding argument has the value `trigger`, then `then`
    /// (e.g. `SetEventMode`'s vararg is `Event` until an `INIT` appears, after which it's `Boolean`).
    SwitchAfter {
        base: EnumType,
        trigger: i32,
        then: EnumType,
    },
}

impl Default for ArgType {
    fn default() -> Self {
        Self::Fixed(EnumType::default())
    }
}

impl From<EnumType> for ArgType {
    fn from(t: EnumType) -> Self {
        Self::Fixed(t)
    }
}

/// Sentinel-accept lists (argument values for which a generic INIT/ON/OFF constant wins).
pub(super) const NO_SENTINEL: &[i32] = &[];
const SENTINEL_INIT: &[i32] = &[-1];
const SENTINEL_OFF: &[i32] = &[0];

impl ArgType {
    /// The representative type for propagating into variables, ignoring value-based conditions.
    pub fn base(&self) -> EnumType {
        match self {
            Self::Fixed(t) | Self::Sentinel { ty: t, .. } => *t,
            Self::Switch { default, .. } => *default,
            Self::SwitchAfter { base, .. } => *base,
        }
    }

    /// Resolve to a concrete type plus the list of argument values eligible for sentinel priority,
    /// given the literal values of all preceding arguments (`None` where an argument wasn't a
    /// literal). The accept list is empty for everything but `Sentinel`.
    pub fn resolve(&self, prior: &[Option<i32>]) -> (EnumType, &'static [i32]) {
        match self {
            Self::Fixed(t) => (*t, NO_SENTINEL),
            Self::Sentinel { ty, accept } => (*ty, accept),
            Self::Switch { on, cases, default } => match prior.get(*on).copied().flatten() {
                None => (EnumType::Any, NO_SENTINEL),
                Some(v) => (
                    cases
                        .iter()
                        .find(|(cv, _)| *cv == v)
                        .map(|(_, t)| *t)
                        .unwrap_or(*default),
                    NO_SENTINEL,
                ),
            },
            Self::SwitchAfter { base, trigger, then } => {
                if prior.iter().flatten().any(|v| v == trigger) {
                    (*then, NO_SENTINEL)
                } else {
                    (*base, NO_SENTINEL)
                }
            }
        }
    }
}

/// Argument-type cases for the value-dependent built-in signatures.
const SET_CHAR_ACTION_CASES: &[(i32, EnumType)] = &[
    (6, EnumType::Animation),    // COMMAND_MOTION
    (12, EnumType::ParamAttack), // COMMAND_ATTACK
    (13, EnumType::ParamKick),   // COMMAND_KICK
    (17, EnumType::ParamWeapon), // COMMAND_WEAPON_ON
    (18, EnumType::ParamWeapon), // COMMAND_WEAPON_OFF
];
/// `SendFunc`'s second argument is a character ID unless the first argument is `1` (null).
const SEND_FUNC_CASES: &[(i32, EnumType)] = &[(1, EnumType::Null)];
/// `SetCameraPos` is overloaded on its leading `CAMERA_*` mode. Its first argument is a character
/// for the character-relative modes (`CHAR`=1, `2CHAR`=2, `CHAR2`=3) but a world coordinate for
/// `WORLD`=0; its second argument is a character only for the two-character mode (`2CHAR`=2).
const CAMERA_POS_ARG1_CASES: &[(i32, EnumType)] = &[
    (1, EnumType::Character), // CAMERA_CHAR
    (2, EnumType::Character), // CAMERA_2CHAR
    (3, EnumType::Character), // CAMERA_CHAR2
];
const CAMERA_POS_ARG2_CASES: &[(i32, EnumType)] = &[(2, EnumType::Character)]; // CAMERA_2CHAR

#[derive(Debug, PartialEq, Clone)]
pub(super) struct Variable(pub String, pub Option<Box<Variable>>); // variable with zero or more attribute accesses

impl Display for Variable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)?;
        if let Some(ref v) = self.1 {
            v.fmt(f)?;
        }

        Ok(())
    }
}

impl FromStr for Variable {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.chars().next().unwrap_or_default() != '#' {
            return Err(anyhow!(
                "Tried to parse variable {} which does not start with #",
                s
            ));
        }

        let rest = &s[1..];
        let (this, attr) = match rest.find('#') {
            Some(attr_pos) => (
                &rest[..attr_pos],
                Some(Box::new(Variable::from_str(&rest[attr_pos..])?)),
            ),
            None => (rest, None),
        };

        Ok(Variable(String::from(this), attr))
    }
}

impl From<&str> for Variable {
    fn from(value: &str) -> Self {
        Self(String::from(value), None)
    }
}

impl From<String> for Variable {
    fn from(value: String) -> Self {
        Self(value, None)
    }
}

/// A mapping of obfuscated function names used in later versions of the game to unobfuscated names
static FUNCTION_OBFUSCATION_MAP: LazyLock<HashMap<&'static str, &'static str>> =
    LazyLock::new(|| {
        hash_map! {
            // event callbacks
            "A00" => "TalkSelect",
            "A01" => "TalkStart",
            "A02" => "TalkEnd",
            "A03" => "TimeOut",
            "A04" => "Watch",
            "A05" => "WeaponOn",
            "A06" => "WeaponOff",
            "A07" => "Join",
            "A08" => "Leave",
            "A09" => "ViewJoin",
            "A0A" => "ViewLeave",
            "A0B" => "PosJoin",
            "A0C" => "PosLeave",
            "A0D" => "Damage",
            "A0E" => "Collision",
            "A0F" => "Down",
            "A10" => "Dead",
            "A11" => "NpcOut",
            "A12" => "MapIn",
            "A13" => "MapOut",
            "A14" => "AIStatus",
            "A15" => "PadAction",
            "A16" => "Start",
            "A17" => "Init",
            "A18" => "SayDead",
            // special(?) functions related to the event system and script interpreter
            "S00" => "ClearFrontEvent",
            "S01" => "Include",
            "S02" => "Stop",
            "S03" => "SetWait",
            "S04" => "SetWaitEndTask",
            "S05" => "SetNoBlock",
            "S06" => "EventStart",
            "S07" => "EventEnd",
            // regular functions
            "C00" => "SetCharAdd",
            "C01" => "SetCharDel",
            "C02" => "SetCharDraw",
            "C03" => "SetCharLife",
            "C04" => "SetCharLifeMax",
            "C05" => "SetCharPos",
            "C06" => "SetCharDir",
            "C07" => "SetCharMove",
            "C08" => "SetCharAction",
            "C09" => "StartCharTrace",
            "C0A" => "StopCharTrace",
            "C0B" => "GetCharStatus",
            "C0C" => "SetCharTarget",
            "C0D" => "SetCharDir2",
            "C0E" => "GetCharPos",
            "C0F" => "GetCharRange",
            "C10" => "GetCharLife",
            "C11" => "GetCharLifeMax",
            "C12" => "SetCharForm",
            "C13" => "SetCharMotion",
            "C14" => "SetCharNoDamageMode",
            "C15" => "GetCharDead",
            "C16" => "SetCharHoldObj",
            "C17" => "SetCharRelObj",
            "C18" => "SetCharNeckAction",
            "C19" => "SetCharStop",
            "C1A" => "GetCharLifeRatio",
            "C1B" => "SetCharFriendFlag",
            "C1C" => "GetCharFriendFlag",
            "C1D" => "GetCharThrowCount",
            "C1E" => "SetCharGroupID",
            "C1F" => "GetCharTargetID",
            "C20" => "SetCharDrawOnList",
            "C21" => "SetCharDrawOffList",
            "C22" => "SetCharNoCollMode",
            "C23" => "SetCharShowList",
            "C24" => "SetCharDead",
            "C25" => "SetCharTalkOver",
            "C26" => "SetCharLevel",
            "C27" => "SetCharPosAdjust",
            "C28" => "SetCharFace",
            "C29" => "SetCharWakiZako",
            "C2A" => "SetCharDirFollow",
            "C2B" => "SetCharDaikonFlag",
            "C2C" => "GetCharDaikonFlag",
            "C2D" => "SubCharDaikonFlag",
            "C2E" => "AddCharDaikonFlag",
            "C2F" => "SetCharDeathBlow",
            "C30" => "SetCharWaiting",
            "C31" => "SetCharDropWeapon",
            "C32" => "SetCharTechFlashMode",
            "C33" => "SetCharExplosion",
            "C34" => "SetCharPosFixMode",
            "C35" => "SetCharHiFaceMode",
            "C36" => "SetCharWeapon",
            "C37" => "SetBattleCamera",
            "C38" => "SetCameraPos",
            "C39" => "SetBustupCamera",
            "C3A" => "SetSoloCamera",
            "C3B" => "SetFixCamera",
            "C3C" => "SetTwoShotCamera",
            "C3D" => "SetVsCamera",
            "C3E" => "SetRotateCamera",
            "C3F" => "SetCutCamera",
            "C40" => "SetCameraMoveSpeed",
            // function C41 is not defined in any known game version
            "C42" => "SetEventMode",
            "C43" => "AddEventMode",
            "C44" => "SubEventMode",
            "C45" => "SetLineAction",
            "C46" => "SetCharWatch",
            "C47" => "SetTimeAction",
            "C48" => "SetExtraAction",
            "C49" => "SetPosLineAction",
            "C4A" => "GetDamageKind",
            "C4B" => "GetCharVisible",
            "C4C" => "SetLineViewAction",
            "C4D" => "SetPadAction",
            "C4E" => "SetCharSayDeadFlag",
            "C4F" => "SePlay",
            "C50" => "BGMPlay",
            "C51" => "BGMStop",
            "C52" => "VoicePlay",
            "C53" => "SetPadMode",
            "C54" => "SetPadCtrl",
            "C55" => "ScreenEffect",
            "C56" => "SetDispDraw",
            "C57" => "GetSamuraiValue",
            "C58" => "SetSamuraiValue",
            "C59" => "AddSamuraiValue",
            "C5A" => "SubSamuraiValue",
            "C5B" => "GetBattleValue",
            "C5C" => "SetBattleValue",
            "C5D" => "GetMapTimeID",
            "C5E" => "SetMapTimeID",
            "C5F" => "GetMapID",
            "C60" => "SetMapID",
            "C61" => "GetMapExitID",
            "C62" => "SetMapExitID",
            "C63" => "GetEventID",
            "C64" => "SetEventID",
            "C65" => "GetPhaseID",
            "C66" => "SetPhaseID",
            "C67" => "SetPlayerFooting",
            "C68" => "GetPlayerFooting",
            "C69" => "SetAddEventScript",
            "C6A" => "SetAddCharScript",
            "C6B" => "SetAddCharScriptList",
            "C6C" => "SetVarInt",
            "C6D" => "GetVarInt",
            "C6E" => "SetVarString",
            "C6F" => "GetVarString",
            "C70" => "SendFunc",
            "C71" => "SendFunc2",
            "C72" => "SetCinemaScope",
            "C73" => "SetFontColor",
            "C74" => "SetSerifWindowColor",
            "C75" => "SetSerifFrameColor",
            "C76" => "SetFilePath",
            "C77" => "ReadEventCharList",
            "C78" => "SetEventUseCharList",
            "C79" => "LoadExecFile",
            "C7A" => "SetMoney",
            "C7B" => "GetMoney",
            "C7C" => "AddMoney",
            "C7D" => "SubMoney",
            "C7E" => "SetGameOver",
            "C7F" => "Reboot",
            "C80" => "SetEventManFlag",
            "C81" => "GetEventManFlag",
            "C82" => "SetEventProFlag",
            "C83" => "GetEventProFlag",
            "C84" => "SetEventActEndFlag",
            "C85" => "GetEventActEndFlag",
            "C86" => "SetHintMessage",
            "C87" => "SetGameStop",
            "C88" => "SetGameClear",
            "C89" => "SetDrawCost",
            "C8A" => "LoadMessage",
            "C8B" => "SetGameScriptPhase",
            "C8C" => "GetValue2String",
            "C8D" => "DelTaskID",
            "C8E" => "GiveMeDaikon",
            "C8F" => "SetWeaponForge",
            "C90" => "SetWeaponHardness",
            "C91" => "SetWeaponDeposit",
            "C92" => "GetWeaponNum",
            "C93" => "CheckWeaponHardness",
            "C94" => "CheckWeaponAttack",
            "C95" => "CheckWeaponDefense",
            "C96" => "ReportWeapon",
            "C97" => "EventEndWait",
            "C98" => "GameStopWait",
            "C99" => "SetMapOutEnd",
            // function C9A is not defined in any known game version
            "C9B" => "PrintFunc",
            "C9C" => "SetAIChar",
            "C9D" => "GetAIChar",
            "C9E" => "DelAIChar",
            "C9F" => "SetAITargetGroup",
            "CA0" => "SetAIAllStop",
            "CA1" => "SetAISiegeLimit",
            "CA2" => "SetAIBackLimit",
            "CA3" => "SetAIWalkLimit",
            "CA4" => "SetAIRunLimit",
            "CA5" => "SetAITargetItem",
            "CA6" => "SetAITargetPos",
            "CA7" => "SetAICharMove",
            "CA8" => "SetAIGroupFooting",
            "CA9" => "SetAIRugbyBall",
            "CAA" => "SetAIGroupRelation",
            "CAB" => "GetAIGroupRelation",
            "CAC" => "Say",
            "CAD" => "SetSayMotion",
            "CAE" => "SetTalkSelect",
            "CAF" => "SayGroup",
            "CB0" => "SetSayPos",
            "CB1" => "SetMapOutSelect",
            "CB2" => "GetObjChar",
            "CB3" => "SetObjPos",
            "CB4" => "AddObjPos",
            "CB5" => "GetObjRangeChar",
            "CB6" => "SetObjDraw",
            "CB7" => "SetObjAction",
            "CB8" => "SetObjMoveTetudo",
            "CB9" => "SetObjRestore",
            "CBA" => "LoadObjSceneData",
            "CBB" => "SetObjStop",
            "CBC" => "SetObjTaihouAction",
            "CBD" => "SetObjTaihouStop",
            "CBE" => "SetNoMapOutFlag",
            "CBF" => "GetNoMapOutFlag",
        }
    });

pub fn deobfuscate(name: &mut String) {
    if let Some(&deobfuscated_name) = FUNCTION_OBFUSCATION_MAP.get(name.as_str()) {
        *name = String::from(deobfuscated_name);
    }
}

// TODO: re-obfuscate

static SIGNATURES: LazyLock<HashMap<&'static str, Signature>> = LazyLock::new(|| {
    hash_map! {
        "ClearFrontEvent" => Signature::args(vec![EnumType::Character]),
        // Include, Stop, SetWait, SetWaitEndTask, SetNoBlock, EventStart, EventEnd have no typed arguments
        "SetCharAdd" => Signature::args(vec![EnumType::Character]),
        "SetCharDel" => Signature::args(vec![EnumType::Character]),
        "SetCharDraw" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SetCharLife" => Signature::args(vec![EnumType::Character]),
        "SetCharLifeMax" => Signature::args(vec![EnumType::Character]),
        // the three coordinates are the character's map-entry (MAPIN) position
        "SetCharPos" => Signature::args(vec![EnumType::Character, EnumType::MapIn, EnumType::MapIn, EnumType::MapIn]),
        // SetCharDir also has a 4-argument form with x, y, z instead of a character, but we don't
        // need special handling for that because a float value won't match to a character constant
        // anyway
        "SetCharDir" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        // after the motion command come the three coordinates of the move goal (MAPOUT)
        "SetCharMove" => Signature::args(vec![EnumType::Character, EnumType::Command, EnumType::MapOut, EnumType::MapOut, EnumType::MapOut]),
        // the third argument's type depends on the COMMAND_* value of the second argument
        "SetCharAction" => Signature::sig(vec![
            ArgType::Fixed(EnumType::Character),
            ArgType::Fixed(EnumType::Command),
            ArgType::Switch { on: 1, cases: SET_CHAR_ACTION_CASES, default: EnumType::Any },
        ]),
        "StartCharTrace" => Signature::args(vec![EnumType::Character, EnumType::Character, EnumType::Command]),
        "StopCharTrace" => Signature::args(vec![EnumType::Character]),
        "GetCharStatus" => Signature::args(vec![EnumType::Character, EnumType::Event]).returns(EnumType::Boolean),
        "SetCharTarget" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        // the two-argument form aims one character at another; the four-argument form aims at an
        // (x, y, z) coordinate instead. Typing the second argument Character is safe for the
        // coordinate form because Character has no float-valued constants.
        "SetCharDir2" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "GetCharPos" => Signature::args(vec![EnumType::Character]),
        // same note as SetCharDir
        "GetCharRange" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "GetCharLife" => Signature::args(vec![EnumType::Character]),
        "GetCharLifeMax" => Signature::args(vec![EnumType::Character]),
        "SetCharForm" => Signature::args(vec![EnumType::Character, EnumType::Boolean, EnumType::Animation]),
        "SetCharMotion" => Signature::args(vec![EnumType::Character, EnumType::Animation, EnumType::Boolean]),
        "SetCharNoDamageMode" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "GetCharDead" => Signature::args(vec![EnumType::Character]).returns(EnumType::Boolean),
        "SetCharHoldObj" => Signature::args(vec![EnumType::Character, EnumType::Object]),
        "SetCharRelObj" => Signature::args(vec![EnumType::Character]),
        "SetCharNeckAction" => Signature::args(vec![EnumType::Character]),
        "SetCharStop" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "GetCharLifeRatio" => Signature::args(vec![EnumType::Character]),
        "SetCharFriendFlag" => Signature::args(vec![EnumType::Character, EnumType::Friend]),
        "GetCharFriendFlag" => Signature::args(vec![EnumType::Character]).returns(EnumType::Friend),
        "GetCharThrowCount" => Signature::args(vec![EnumType::Character]),
        "SetCharGroupID" => Signature::args(vec![EnumType::Character, EnumType::Footing]),
        "GetCharTargetID" => Signature::args(vec![EnumType::Character]).returns(EnumType::Character),
        "SetCharDrawOnList" => Signature::varargs(EnumType::Character),
        "SetCharDrawOffList" => Signature::varargs(EnumType::Character),
        "SetCharNoCollMode" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SetCharShowList" => Signature::args(vec![EnumType::Boolean]).vararg(EnumType::Character),
        "SetCharDead" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SetCharTalkOver" => Signature::args(vec![EnumType::Character]),
        "SetCharLevel" => Signature::args(vec![EnumType::Character]),
        "SetCharPosAdjust" => Signature::args(vec![EnumType::Character]),
        "SetCharFace" => Signature::args(vec![EnumType::Character, EnumType::Animation]),
        "SetCharWakiZako" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SetCharDirFollow" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "SetCharDaikonFlag" => Signature::args(vec![EnumType::Character]),
        "GetCharDaikonFlag" => Signature::args(vec![EnumType::Character]),
        "SubCharDaikonFlag" => Signature::args(vec![EnumType::Character]),
        "AddCharDaikonFlag" => Signature::args(vec![EnumType::Character]),
        "SetCharDeathBlow" => Signature::args(vec![EnumType::Character]),
        "SetCharWaiting" => Signature::args(vec![EnumType::Character]),
        "SetCharDropWeapon" => Signature::args(vec![EnumType::Character]),
        "SetCharTechFlashMode" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SetCharExplosion" => Signature::args(vec![EnumType::Character]),
        "SetCharPosFixMode" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SetCharHiFaceMode" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SetCharWeapon" => Signature::args(vec![EnumType::Character]),
        "SetBattleCamera" => Signature::args(vec![EnumType::Boolean]),
        // a lone Camera argument of -1 is the generic INIT sentinel, not CAMERA_INIT; the next two
        // arguments are character ids or world coordinates depending on the camera mode (see cases)
        "SetCameraPos" => Signature::sig(vec![
            ArgType::Sentinel { ty: EnumType::Camera, accept: SENTINEL_INIT },
            ArgType::Switch { on: 0, cases: CAMERA_POS_ARG1_CASES, default: EnumType::Any },
            ArgType::Switch { on: 0, cases: CAMERA_POS_ARG2_CASES, default: EnumType::Any },
        ]),
        "SetBustupCamera" => Signature::args(vec![EnumType::Character]),
        "SetSoloCamera" => Signature::args(vec![EnumType::Character]),
        "SetFixCamera" => Signature::args(vec![EnumType::Character]),
        "SetTwoShotCamera" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "SetVsCamera" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        // SetRotateCamera has no typed arguments
        "SetCutCamera" => Signature::sig(vec![ArgType::Sentinel { ty: EnumType::Camera, accept: SENTINEL_INIT }]),
        // SetCameraMoveSpeed has no typed arguments
        // the event-mode vararg is normally an Event, but a leading INIT switches the remaining
        // arguments to booleans (the reset form `SetEventMode char, INIT, ON/OFF`)
        "SetEventMode" => Signature::args(vec![EnumType::Character])
            .vararg_t(ArgType::SwitchAfter { base: EnumType::Event, trigger: -1, then: EnumType::Boolean }),
        "AddEventMode" => Signature::args(vec![EnumType::Character])
            .vararg_t(ArgType::SwitchAfter { base: EnumType::Event, trigger: -1, then: EnumType::Boolean }),
        "SubEventMode" => Signature::args(vec![EnumType::Character])
            .vararg_t(ArgType::SwitchAfter { base: EnumType::Event, trigger: -1, then: EnumType::Boolean }),
        "SetLineAction" => Signature::args(vec![EnumType::Character]),
        "SetCharWatch" => Signature::args(vec![EnumType::Character, EnumType::Character, EnumType::Watch, EnumType::Any, EnumType::Object]),
        // the third argument is a duration in seconds; -1.0 is the INIT_TIME sentinel
        "SetTimeAction" => Signature::args(vec![EnumType::Character, EnumType::Character, EnumType::Duration]),
        // SetExtraAction has no typed arguments
        // the first argument is a line/function id (not a character); the next three coordinates
        // are the move goal (MAPOUT), or #INIT to clear
        "SetPosLineAction" => Signature::sig(vec![
            ArgType::Fixed(EnumType::Any),
            ArgType::Sentinel { ty: EnumType::MapOut, accept: SENTINEL_INIT },
            ArgType::Fixed(EnumType::MapOut),
            ArgType::Fixed(EnumType::MapOut),
        ]),
        "GetDamageKind" => Signature::args(vec![EnumType::Character]).returns(EnumType::Damage),
        "GetCharVisible" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "SetLineViewAction" => Signature::args(vec![EnumType::Character]),
        "SetPadAction" => Signature::args(vec![EnumType::Button]),
        "SetCharSayDeadFlag" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SePlay" => Signature::args(vec![EnumType::Any, EnumType::Any, EnumType::Character]),
        // BGMPlay has no typed arguments
        // BGMStop has no typed arguments
        "VoicePlay" => Signature::args(vec![EnumType::Any, EnumType::Any, EnumType::Character]),
        "SetPadMode" => Signature::args(vec![EnumType::Boolean, EnumType::Boolean, EnumType::Boolean]),
        // SetPadCtrl has no typed arguments
        "ScreenEffect" => Signature::args(vec![EnumType::Effect, EnumType::FadeDir, EnumType::FadeType]),
        // SetDispDraw has no typed arguments
        "GetSamuraiValue" => Signature::args(vec![EnumType::Character]),
        "SetSamuraiValue" => Signature::args(vec![EnumType::Character]),
        "AddSamuraiValue" => Signature::args(vec![EnumType::Character]),
        "SubSamuraiValue" => Signature::args(vec![EnumType::Character]),
        "GetBattleValue" => Signature::args(vec![EnumType::Character]),
        "SetBattleValue" => Signature::args(vec![EnumType::Character]),
        "GetMapTimeID" => Signature::args(vec![]).returns(EnumType::Time),
        "SetMapTimeID" => Signature::args(vec![EnumType::Time]),
        "GetMapID" => Signature::args(vec![]).returns(EnumType::Map),
        "SetMapID" => Signature::args(vec![EnumType::Map]),
        // GetMapExitID, SetMapExitID, GetEventID, SetEventID, GetPhaseID, SetPhaseID have no typed arguments
        "SetPlayerFooting" => Signature::args(vec![EnumType::Footing]),
        "GetPlayerFooting" => Signature::args(vec![]).returns(EnumType::Footing),
        // SetAddEventScript has no typed arguments
        "SetAddCharScript" => Signature::args(vec![EnumType::Character]),
        "SetAddCharScriptList" => Signature::args(vec![EnumType::Any]).vararg(EnumType::Character),
        // SetVarInt, GetVarInt, SetVarString, GetVarString have no typed arguments
        // the second argument is a character ID unless the first (selector) argument is 1 (null)
        "SendFunc" => Signature::sig(vec![
            ArgType::Fixed(EnumType::Any),
            ArgType::Switch { on: 0, cases: SEND_FUNC_CASES, default: EnumType::Character },
        ]),
        "SendFunc2" => Signature::sig(vec![
            ArgType::Fixed(EnumType::Any),
            ArgType::Switch { on: 0, cases: SEND_FUNC_CASES, default: EnumType::Character },
        ]),
        "SetCinemaScope" => Signature::args(vec![EnumType::Boolean]),
        // SetFontColor, SetSerifWindowColor, SetSerifFrameColor, SetFilePath, ReadEventCharList have no typed arguments
        "SetEventUseCharList" => Signature::varargs(EnumType::Character),
        // LoadExecFile, SetMoney, GetMoney, AddMoney, SubMoney, SetGameOver, Reboot, SetEventManFlag,
        // GetEventManFlag have no typed arguments
        "SetEventProFlag" => Signature::args(vec![EnumType::Any, EnumType::EventProgress]),
        "GetEventProFlag" => Signature::args(vec![EnumType::Any]).returns(EnumType::EventProgress),
        // SetEventActEndFlag, GetEventActEndFlag, SetHintMessage, SetGameStop, SetGameClear, SetDrawCost,
        // LoadMessage, SetGameScriptPhase, GetValue2String, DelTaskID have no typed arguments
        "GiveMeDaikon" => Signature::args(vec![EnumType::Character]),
        // SetWeaponForge, SetWeaponHardness, SetWeaponDeposit, GetWeaponNum, CheckWeaponHardness, CheckWeaponAttack,
        // CheckWeaponDefense, ReportWeapon, EventEndWait, GameStopWait, SetMapOutEnd, PrintFunc have no typed arguments
        "SetAIChar" => Signature::args(vec![EnumType::Character, EnumType::Ai]),
        "GetAIChar" => Signature::args(vec![EnumType::Character]).returns(EnumType::Ai),
        "DelAIChar" => Signature::args(vec![EnumType::Character]),
        // SetAITargetGroup has no typed arguments
        "SetAIAllStop" => Signature::args(vec![EnumType::Boolean]),
        "SetAISiegeLimit" => Signature::args(vec![EnumType::Character]),
        "SetAIBackLimit" => Signature::args(vec![EnumType::Character]),
        "SetAIWalkLimit" => Signature::args(vec![EnumType::Character]),
        "SetAIRunLimit" => Signature::args(vec![EnumType::Character]),
        "SetAITargetItem" => Signature::args(vec![EnumType::Character, EnumType::Object]),
        "SetAITargetPos" => Signature::args(vec![EnumType::Character]),
        // after the motion command come the three coordinates of the move goal (MAPOUT)
        "SetAICharMove" => Signature::args(vec![EnumType::Character, EnumType::Command, EnumType::MapOut, EnumType::MapOut, EnumType::MapOut]),
        "SetAIGroupFooting" => Signature::args(vec![EnumType::Any, EnumType::Footing]),
        "SetAIRugbyBall" => Signature::args(vec![EnumType::Object]),
        "SetAIGroupRelation" => Signature::args(vec![EnumType::Footing, EnumType::Footing, EnumType::Relation]),
        "GetAIGroupRelation" => Signature::args(vec![EnumType::Footing, EnumType::Footing]).returns(EnumType::Relation),
        "Say" => Signature::args(vec![EnumType::Character, EnumType::Character, EnumType::Any, EnumType::Any, EnumType::Any, EnumType::Say]),
        // arg 2 is an animation, except value 0 which is the OFF sentinel; arg 3 is a boolean
        "SetSayMotion" => Signature::sig(vec![
            ArgType::Fixed(EnumType::Character),
            ArgType::Sentinel { ty: EnumType::Animation, accept: SENTINEL_OFF },
            ArgType::Fixed(EnumType::Boolean),
        ]),
        "SetTalkSelect" => Signature::args(vec![EnumType::Character]),
        "SayGroup" => Signature::args(vec![EnumType::Character, EnumType::Any, EnumType::Any, EnumType::Any, EnumType::Say]).vararg(EnumType::Character),
        "SetSayPos" => Signature::args(vec![EnumType::Character]),
        // SetMapOutSelect has no typed arguments
        "GetObjChar" => Signature::args(vec![EnumType::Character]).returns(EnumType::Object),
        "SetObjPos" => Signature::args(vec![EnumType::Object]),
        "AddObjPos" => Signature::args(vec![EnumType::Object]),
        "GetObjRangeChar" => Signature::args(vec![EnumType::Object, EnumType::Character]).returns(EnumType::Boolean),
        "SetObjDraw" => Signature::args(vec![EnumType::Object, EnumType::Boolean]),
        "SetObjAction" => Signature::args(vec![EnumType::Object]),
        "SetObjMoveTetudo" => Signature::args(vec![EnumType::Boolean]),
        // SetObjRestore has no typed arguments
        "LoadObjSceneData" => Signature::args(vec![EnumType::ObjectSet]),
        "SetObjStop" => Signature::args(vec![EnumType::Object]),
        // SetObjTaihouAction, SetObjTaihouStop have no typed arguments
        "SetNoMapOutFlag" => Signature::args(vec![EnumType::Boolean]),
        "GetNoMapOutFlag" => Signature::args(vec![]).returns(EnumType::Boolean),
        // SetDemoEnd, GetVSRand have no typed arguments
        // callback functions
        "MapIn" => Signature::args(vec![EnumType::Map]),
        "MapOut" => Signature::args(vec![EnumType::Map]),
        "Collision" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "Damage" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "Down" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "TalkStart" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "TalkEnd" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "TalkSelect" => Signature::args(vec![EnumType::Character]),
        "PosJoin" => Signature::args(vec![EnumType::Character]),
        "PosLeave" => Signature::args(vec![EnumType::Character]),
        "Join" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "Leave" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "ViewJoin" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "ViewLeave" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "TimeOut" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "SayDead" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "NpcOut" => Signature::args(vec![EnumType::Character]),
        "WeaponOn" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "WeaponOff" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "Dead" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "Watch" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "PadAction" => Signature::args(vec![EnumType::Button]),
        "AIStatus" => Signature::args(vec![EnumType::Character, EnumType::Ai]),
    }
});

#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub(super) struct Signature {
    arguments: Vec<ArgType>,
    vararg: ArgType,
    return_type: EnumType,
}

impl Signature {
    /// Build a signature from a list of plain (`Fixed`) argument types.
    pub fn args(arguments: Vec<EnumType>) -> Self {
        Self {
            arguments: arguments.into_iter().map(ArgType::Fixed).collect(),
            vararg: ArgType::default(),
            return_type: EnumType::default(),
        }
    }

    /// Build a signature whose arguments use the richer `ArgType` resolution rules.
    pub fn sig(arguments: Vec<ArgType>) -> Self {
        Self {
            arguments,
            vararg: ArgType::default(),
            return_type: EnumType::default(),
        }
    }

    pub fn varargs(arg_type: EnumType) -> Self {
        Self {
            arguments: vec![],
            vararg: ArgType::Fixed(arg_type),
            return_type: EnumType::default(),
        }
    }

    pub fn vararg(mut self, arg_type: EnumType) -> Self {
        self.vararg = ArgType::Fixed(arg_type);
        self
    }

    pub fn vararg_t(mut self, arg_type: ArgType) -> Self {
        self.vararg = arg_type;
        self
    }

    pub fn returns(mut self, return_type: EnumType) -> Self {
        self.return_type = return_type;
        self
    }

    /// The `ArgType` rule for the argument at `index`, falling back to the vararg rule for
    /// positions past the end of the fixed argument list.
    pub fn arg_type(&self, index: usize) -> ArgType {
        self.arguments
            .get(index)
            .cloned()
            .unwrap_or_else(|| self.vararg.clone())
    }

    /// Merge an inferred type (and optional sentinel `accept` list) into argument `index`, growing
    /// the argument list as needed. Inferred arguments are `Fixed` unless an `accept` list is
    /// supplied — a parameter that flows into a built-in's `Sentinel` argument (e.g. SAY's motion
    /// arg into `SetSayMotion`) keeps that sentinel so a value-0 argument restores `#OFF` rather
    /// than the generic `#NULL`. Returns whether the argument's resolution actually changed.
    pub fn infer_argument(&mut self, index: usize, arg_type: EnumType, accept: &'static [i32]) -> bool {
        if index >= self.arguments.len() {
            self.arguments.resize_with(index + 1, ArgType::default);
        }
        let base = self.arguments[index].base().choose(arg_type);
        let resolved = if accept.is_empty() {
            ArgType::Fixed(base)
        } else {
            ArgType::Sentinel { ty: base, accept }
        };
        let changed = self.arguments[index] != resolved;
        self.arguments[index] = resolved;
        changed
    }

    pub fn return_type(&self) -> EnumType {
        self.return_type
    }

    /// Set the return type of this function to the provided return type if the new type is not
    /// less specific than the old type.
    pub fn update_return_type(&mut self, new_return_type: EnumType) -> EnumType {
        self.return_type.update(new_return_type)
    }

    pub fn merge<T: Deref<Target = Self>>(&mut self, other: T) {
        // only plain `Fixed` arguments (inferred user functions) are merged; conditional built-in
        // rules are preserved as-is
        for (our_arg, their_arg) in self.arguments.iter_mut().zip(other.arguments.iter()) {
            match (&*our_arg, their_arg) {
                // a plain `Fixed` arg adopts the other side's inferred `Sentinel` (e.g. SAY's
                // motion arg, recovered through a list slot, must keep its `0→OFF` behavior
                // across the re-declarations that reprocessing a `?F` definition produces)
                (ArgType::Fixed(our), ArgType::Sentinel { ty, accept }) => {
                    *our_arg = ArgType::Sentinel { ty: our.choose(*ty), accept };
                }
                (ArgType::Fixed(our), _) => {
                    *our_arg = ArgType::Fixed(our.choose(their_arg.base()));
                }
                // our side already carries a conditional rule (built-in `Switch`/`Sentinel` or an
                // inferred `Sentinel`); preserve it as-is
                _ => {}
            }
        }
        if other.arguments.len() > self.arguments.len() {
            self.arguments
                .extend_from_slice(&other.arguments[self.arguments.len()..]);
        }
        if let ArgType::Fixed(vararg) = &mut self.vararg {
            *vararg = vararg.choose(other.vararg.base());
        }
        self.return_type.update(other.return_type);
    }
}

pub(super) type SharedScope = Rc<RefCell<Scope>>;
pub(super) type SharedSignature = Rc<RefCell<Signature>>;

#[derive(Debug)]
pub(super) enum ScriptValue {
    Scalar(EnumType),
    Function(SharedSignature),
    Object(SharedScope),
}

impl ScriptValue {
    pub fn get_type(&self) -> EnumType {
        match self {
            &Self::Scalar(t) => t,
            Self::Function(sig) => sig.borrow().return_type(),
            _ => EnumType::default(),
        }
    }
}

impl Clone for ScriptValue {
    fn clone(&self) -> Self {
        match self {
            &Self::Scalar(t) => Self::Scalar(t),
            Self::Function(sig) => Self::Function(Rc::new(RefCell::new(sig.borrow().clone()))),
            Self::Object(scope) => Self::Object(Rc::new(RefCell::new(scope.borrow().clone()))),
        }
    }
}

macro_rules! parent {
    ($scope:ident, $method:ident($($arg:expr),*)) => {
        $scope.parent.as_ref().and_then(Weak::upgrade).and_then(|p| p.borrow().$method($($arg),*))
    };
}

#[derive(Debug, Clone)]
pub(super) struct Scope {
    scalars: HashMap<String, EnumType>,
    // sentinel `accept` lists for scalars that were typed by flowing into a built-in's `Sentinel`
    // argument (chiefly user-defined method parameters routed through a list slot, e.g. SAY's
    // motion arg into `SetSayMotion`). Kept parallel to `scalars` so the inferred signature can
    // preserve the `0→OFF`/`-1→INIT` behavior rather than collapsing to a plain `Fixed` type.
    scalar_sentinels: HashMap<String, &'static [i32]>,
    // since our parent scope is in a RefCell, any type we want to be able to return a reference to
    // has to be in an Rc, because there's no other way to get a permanent reference to anything in
    // our maps out of the parent RefCell
    functions: HashMap<String, SharedSignature>,
    // either the object references or the parent reference need to be weak to avoid a cycle. we'll
    // make the parent weak because object variables need to be owned by the scope, as they have
    // no other owner
    objects: HashMap<String, SharedScope>,
    parent: Option<Weak<RefCell<Scope>>>,
}

impl Scope {
    pub fn new(parent: Option<SharedScope>) -> SharedScope {
        Rc::new(RefCell::new(Self {
            scalars: HashMap::new(),
            scalar_sentinels: HashMap::new(),
            functions: HashMap::new(),
            objects: HashMap::new(),
            parent: parent.as_ref().map(Rc::downgrade),
        }))
    }

    pub fn new_global(constants: Option<HashMap<String, EnumType>>) -> SharedScope {
        let mut functions = HashMap::new();
        for (&name, signature) in SIGNATURES.iter() {
            functions.insert(String::from(name), Rc::new(RefCell::new(signature.clone())));
        }

        let this = Rc::new(RefCell::new(Self {
            scalars: constants.unwrap_or_default(),
            scalar_sentinels: HashMap::new(),
            functions,
            objects: HashMap::new(),
            parent: None,
        }));

        this.borrow_mut()
            .objects
            .insert(String::from("object"), this.new_child());
        this
    }

    pub fn merge<T: Deref<Target = Self>>(&mut self, other: T) {
        if std::ptr::eq(self, &*other) {
            return; // nothing to do
        }

        for (name, &new_value) in &other.scalars {
            match self.scalars.get_mut(name) {
                Some(value) => {
                    *value = value.choose(new_value);
                }
                None => {
                    self.scalars.insert(name.clone(), new_value);
                }
            }
        }

        for (name, &accept) in &other.scalar_sentinels {
            self.scalar_sentinels.entry(name.clone()).or_insert(accept);
        }

        for (name, new_value) in &other.functions {
            match self.functions.get_mut(name) {
                Some(value) => {
                    if std::ptr::eq(value.as_ptr(), new_value.as_ptr()) {
                        continue;
                    }

                    value.borrow_mut().merge(new_value.borrow());
                }
                None => {
                    self.functions.insert(name.clone(), Rc::clone(new_value));
                }
            }
        }

        for (name, new_value) in &other.objects {
            match self.objects.get_mut(name) {
                Some(value) => {
                    if std::ptr::eq(value.as_ptr(), new_value.as_ptr()) {
                        continue;
                    }

                    value.borrow_mut().merge(new_value.borrow());
                }
                None => {
                    self.objects.insert(name.clone(), Rc::clone(new_value));
                }
            }
        }
    }

    pub fn parent(&self) -> Option<SharedScope> {
        self.parent.as_ref().and_then(Weak::upgrade)
    }

    // I've decided not to make this an Option for now because I can't currently envision a
    // scenario where we would change the global scope to not be the global scope
    pub fn set_parent(&mut self, parent: SharedScope) {
        if std::ptr::eq(parent.as_ptr(), self) {
            panic!("Tried to set parent to self");
        }
        self.parent = Some(Rc::downgrade(&parent));
    }

    fn lookup_for_attribute<'a, 'b, F>(
        this: &'a SharedScope,
        var: &'b Variable,
        lookup: F,
    ) -> (Option<SharedScope>, &'b str)
    where
        F: FnOnce(&Self, &'b str) -> Option<SharedScope>,
    {
        match var {
            Variable(name, None) => (None, name),
            Variable(name, Some(attr)) => {
                let mut this_mut = this.borrow_mut();
                let base_object = lookup(&this_mut, name).unwrap_or_else(|| {
                    let new_object = this.new_child();
                    this_mut
                        .objects
                        .insert(name.clone(), Rc::clone(&new_object));
                    new_object
                });
                let (sub_object, final_name) =
                    Self::get_attribute_for_attribute(&base_object, attr.as_ref());
                (
                    Some(sub_object.unwrap_or_else(|| Rc::clone(this))),
                    final_name,
                )
            }
        }
    }

    fn get_attribute_for_attribute<'a>(
        this: &SharedScope,
        var: &'a Variable,
    ) -> (Option<SharedScope>, &'a str) {
        Self::lookup_for_attribute(this, var, Self::lookup_own_object)
    }

    fn get_object_for_attribute_local<'a>(
        this: &SharedScope,
        var: &'a Variable,
    ) -> (SharedScope, &'a str) {
        let (object, name) =
            Self::lookup_for_attribute(this, var, |this, name| this.lookup_object_local(name));
        (object.unwrap_or_else(|| Rc::clone(this)), name)
    }

    fn get_object_for_attribute_global<'a>(
        this: &SharedScope,
        var: &'a Variable,
    ) -> (SharedScope, &'a str) {
        let (object, name) =
            Self::lookup_for_attribute(this, var, |this, name| this.lookup_object_global(name));
        (object.unwrap_or_else(|| Rc::clone(this)), name)
    }

    fn lookup_attribute_definition_scope(
        attr: &Variable,
        scope: Option<SharedScope>,
    ) -> Option<(Option<SharedScope>, &str)> {
        scope.and_then(|obj_scope| {
            let mut sub = attr;
            let mut next_scope = Some(obj_scope);
            while let (Some(scope), Variable(attr_name, Some(next_attr))) =
                (next_scope.as_ref().map(Rc::clone), sub)
            {
                next_scope = scope.borrow().lookup_own_object(attr_name);
                sub = next_attr;
            }
            next_scope
                .filter(|s| {
                    let scope_ref = s.borrow();
                    scope_ref.scalars.contains_key(&sub.0)
                        || scope_ref.functions.contains_key(&sub.0)
                        || scope_ref.objects.contains_key(&sub.0)
                })
                .map(|s| (Some(s), sub.0.as_str()))
        })
    }

    fn lookup_definition_scope_local<'a>(
        &self,
        var: &'a Variable,
    ) -> Option<(Option<SharedScope>, &'a str)> {
        match var {
            Variable(name, None) => {
                if self.objects.contains_key(name)
                    || self.functions.contains_key(name)
                    || self.scalars.contains_key(name)
                {
                    Some((None, name.as_str()))
                } else {
                    match parent!(self, lookup_definition_scope_local(var)) {
                        Some((None, name)) => Some((self.parent(), name)),
                        result => result,
                    }
                }
            }
            Variable(name, Some(attr)) => Self::lookup_attribute_definition_scope(
                attr,
                self.lookup_local_object(&name.as_str().into()),
            ),
        }
    }

    fn lookup_definition_scope_global<'a>(
        &self,
        var: &'a Variable,
    ) -> Option<(Option<SharedScope>, &'a str)> {
        match var {
            Variable(name, None) => match parent!(self, lookup_definition_scope_global(var)) {
                Some((None, _)) => Some((self.parent(), name.as_str())),
                None => {
                    if self.objects.contains_key(name)
                        || self.functions.contains_key(name)
                        || self.scalars.contains_key(name)
                    {
                        Some((None, name.as_str()))
                    } else {
                        None
                    }
                }
                scope => scope,
            },
            Variable(name, Some(attr)) => Self::lookup_attribute_definition_scope(
                attr,
                self.lookup_global_object(&name.as_str().into()),
            ),
        }
    }

    fn add_scalar(&mut self, name: &str, scalar_type: EnumType) {
        self.objects.remove(name);
        self.functions.remove(name);
        let old_type = self.scalars.get(name).copied().unwrap_or_default();
        self.scalars
            .insert(String::from(name), old_type.choose(scalar_type));
    }

    fn add_scalar_sentinel(&mut self, name: &str, accept: &'static [i32]) {
        // keep the first sentinel recorded for this scalar (sentinel-bearing reads of the same slot
        // agree in practice; this just avoids thrashing the fixpoint)
        self.scalar_sentinels
            .entry(String::from(name))
            .or_insert(accept);
    }

    fn add_function(&mut self, name: &str, signature: SharedSignature) {
        self.objects.remove(name);
        self.scalars.remove(name);
        if let Some(old_sig) = self.functions.get(name) {
            signature.borrow_mut().merge(old_sig.borrow());
        }
        self.functions.insert(String::from(name), signature);
    }

    fn add_object(&mut self, name: &str, attributes: SharedScope) {
        self.scalars.remove(name);
        self.functions.remove(name);
        match self.objects.get_mut(name) {
            Some(scope) => {
                scope.borrow_mut().merge(attributes.borrow());
            }
            None => {
                self.objects.insert(String::from(name), attributes);
            }
        }
    }

    fn add(&mut self, name: &str, value: ScriptValue) {
        match value {
            ScriptValue::Scalar(scalar) => self.add_scalar(name, scalar),
            ScriptValue::Function(signature) => self.add_function(name, signature),
            ScriptValue::Object(attributes) => self.add_object(name, attributes),
        }
    }

    pub fn lookup_own_scalar(&self, name: &str) -> Option<EnumType> {
        self.scalars.get(name).copied()
    }

    pub fn lookup_own_scalar_sentinel(&self, name: &str) -> Option<&'static [i32]> {
        self.scalar_sentinels.get(name).copied()
    }

    pub fn lookup_own_function(&self, name: &str) -> Option<SharedSignature> {
        self.functions.get(name).map(Rc::clone)
    }

    fn lookup_own_object(&self, name: &str) -> Option<SharedScope> {
        self.objects.get(name).map(Rc::clone)
    }

    fn lookup_own_var(&self, name: &str) -> Option<ScriptValue> {
        if let Some(scalar) = self.lookup_own_scalar(name) {
            Some(ScriptValue::Scalar(scalar))
        } else if let Some(object) = self.lookup_own_object(name) {
            Some(ScriptValue::Object(object))
        } else {
            self.lookup_own_function(name).map(ScriptValue::Function)
        }
    }

    fn lookup_object_local(&self, name: &str) -> Option<SharedScope> {
        self.lookup_own_object(name)
            .or_else(|| parent!(self, lookup_object_local(name)))
    }

    fn lookup_object_global(&self, name: &str) -> Option<SharedScope> {
        parent!(self, lookup_object_global(name)).or_else(|| self.lookup_own_object(name))
    }

    fn lookup_function_local(&self, name: &str) -> Option<SharedSignature> {
        self.lookup_own_function(name)
            .or_else(|| parent!(self, lookup_function_local(name)))
    }

    fn lookup_function_global(&self, name: &str) -> Option<SharedSignature> {
        parent!(self, lookup_function_global(name)).or_else(|| self.lookup_own_function(name))
    }

    fn lookup_var_local(&self, name: &str) -> Option<ScriptValue> {
        self.lookup_own_var(name)
            .or_else(|| parent!(self, lookup_var_local(name)))
    }

    fn lookup_var_global(&self, name: &str) -> Option<ScriptValue> {
        parent!(self, lookup_var_global(name)).or_else(|| self.lookup_var_local(name))
    }

    pub fn lookup_function_attribute(&self, var: &Variable) -> Option<SharedSignature> {
        match var {
            Variable(name, None) => self.lookup_own_function(name),
            Variable(name, Some(attr)) => self
                .lookup_own_object(name)
                .and_then(|o| o.borrow().lookup_function_attribute(attr.as_ref())),
        }
    }

    pub fn lookup_object_attribute(&self, var: &Variable) -> Option<SharedScope> {
        match var {
            Variable(name, None) => self.lookup_own_object(name),
            Variable(name, Some(attr)) => self
                .lookup_own_object(name)
                .and_then(|o| o.borrow().lookup_object_attribute(attr.as_ref())),
        }
    }

    pub fn lookup_attribute(&self, var: &Variable) -> Option<ScriptValue> {
        match var {
            Variable(name, None) => self.lookup_own_var(name),
            Variable(name, Some(attr)) => self
                .lookup_own_object(name)
                .and_then(|o| o.borrow().lookup_attribute(attr.as_ref())),
        }
    }

    pub fn lookup_local_function(&self, var: &Variable) -> Option<SharedSignature> {
        match var {
            Variable(name, None) => self.lookup_function_local(name),
            Variable(name, Some(attr)) => self
                .lookup_object_local(name)
                .and_then(|o| o.borrow().lookup_function_attribute(attr.as_ref())),
        }
    }

    pub fn lookup_global_function(&self, var: &Variable) -> Option<SharedSignature> {
        match var {
            Variable(name, None) => self.lookup_function_global(name),
            Variable(name, Some(attr)) => self
                .lookup_object_global(name)
                .and_then(|o| o.borrow().lookup_function_attribute(attr.as_ref())),
        }
    }

    pub fn lookup_local_object(&self, var: &Variable) -> Option<SharedScope> {
        match var {
            Variable(name, None) => self.lookup_object_local(name),
            Variable(name, Some(attr)) => self
                .lookup_object_local(name)
                .and_then(|o| o.borrow().lookup_object_attribute(attr.as_ref())),
        }
    }

    pub fn lookup_global_object(&self, var: &Variable) -> Option<SharedScope> {
        match var {
            Variable(name, None) => self.lookup_object_global(name),
            Variable(name, Some(attr)) => self
                .lookup_object_global(name)
                .and_then(|o| o.borrow().lookup_object_attribute(attr.as_ref())),
        }
    }

    pub fn lookup_local_method(&self, var: &Variable, method: &str) -> Option<SharedSignature> {
        self.lookup_local_object(var)
            .and_then(|o| o.borrow().lookup_own_function(method))
    }

    pub fn lookup_global_method(&self, var: &Variable, method: &str) -> Option<SharedSignature> {
        self.lookup_global_object(var)
            .and_then(|o| o.borrow().lookup_own_function(method))
    }

    pub fn lookup_local(&self, var: &Variable) -> Option<ScriptValue> {
        match var {
            Variable(name, None) => self.lookup_var_local(name),
            Variable(name, Some(attr)) => self
                .lookup_object_local(name)
                .and_then(|o| o.borrow().lookup_attribute(attr.as_ref())),
        }
    }

    pub fn lookup_global(&self, var: &Variable) -> Option<ScriptValue> {
        match var {
            Variable(name, None) => self.lookup_var_global(name),
            Variable(name, Some(attr)) => self
                .lookup_object_global(name)
                .and_then(|o| o.borrow().lookup_attribute(attr.as_ref())),
        }
    }

    pub fn lookup_function(&self, var: &Variable, is_global: bool) -> Option<SharedSignature> {
        if is_global {
            self.lookup_global_function(var)
        } else {
            self.lookup_local_function(var)
        }
    }

    pub fn lookup_object(&self, var: &Variable, is_global: bool) -> Option<SharedScope> {
        if is_global {
            self.lookup_global_object(var)
        } else {
            self.lookup_local_object(var)
        }
    }

    pub fn lookup_method(
        &self,
        var: &Variable,
        method: &str,
        is_global: bool,
    ) -> Option<SharedSignature> {
        if is_global {
            self.lookup_global_method(var, method)
        } else {
            self.lookup_local_method(var, method)
        }
    }

    pub fn lookup(&self, var: &Variable, is_global: bool) -> Option<ScriptValue> {
        if is_global {
            self.lookup_global(var)
        } else {
            self.lookup_local(var)
        }
    }

    pub fn update_local_scalar(&mut self, var: &Variable, scalar_type: EnumType) {
        match self.lookup_definition_scope_local(var) {
            Some((Some(scope), name)) => {
                scope.borrow_mut().add_scalar(name, scalar_type);
            }
            Some((None, name)) => {
                self.add_scalar(name, scalar_type);
            }
            None => (),
        }
    }

    pub fn update_global_scalar(&mut self, var: &Variable, scalar_type: EnumType) {
        match self.lookup_definition_scope_global(var) {
            Some((Some(scope), name)) => {
                scope.borrow_mut().add_scalar(name, scalar_type);
            }
            Some((None, name)) => {
                self.add_scalar(name, scalar_type);
            }
            None => (),
        }
    }

    /// Record that the scalar `var` carries a sentinel `accept` list, stored on the scalar's
    /// defining scope (mirroring `update_local_scalar`). Used to remember that a method parameter
    /// flowed into a `Sentinel` argument so the inferred signature can reproduce it.
    pub fn update_scalar_sentinel(&mut self, var: &Variable, is_global: bool, accept: &'static [i32]) {
        let definition_scope = if is_global {
            self.lookup_definition_scope_global(var)
        } else {
            self.lookup_definition_scope_local(var)
        };
        match definition_scope {
            Some((Some(scope), name)) => {
                scope.borrow_mut().add_scalar_sentinel(name, accept);
            }
            Some((None, name)) => {
                self.add_scalar_sentinel(name, accept);
            }
            None => (),
        }
    }

    pub fn update_local_function(&mut self, var: &Variable, signature: SharedSignature) {
        match self.lookup_definition_scope_local(var) {
            Some((Some(scope), name)) => {
                scope.borrow_mut().add_function(name, signature);
            }
            Some((None, name)) => {
                self.add_function(name, signature);
            }
            None => (),
        }
    }

    pub fn update_global_function(&mut self, var: &Variable, signature: SharedSignature) {
        match self.lookup_definition_scope_global(var) {
            Some((Some(scope), name)) => {
                scope.borrow_mut().add_function(name, signature);
            }
            Some((None, name)) => {
                self.add_function(name, signature);
            }
            None => (),
        }
    }

    pub fn update_local_object(&mut self, var: &Variable, attributes: SharedScope) {
        match self.lookup_definition_scope_local(var) {
            Some((Some(scope), name)) => {
                scope.borrow_mut().add_object(name, attributes);
            }
            Some((None, name)) => {
                self.add_object(name, attributes);
            }
            None => (),
        }
    }

    pub fn update_global_object(&mut self, var: &Variable, attributes: SharedScope) {
        match self.lookup_definition_scope_global(var) {
            Some((Some(scope), name)) => {
                scope.borrow_mut().add_object(name, attributes);
            }
            Some((None, name)) => {
                self.add_object(name, attributes);
            }
            None => (),
        }
    }

    pub fn update_local(&mut self, var: &Variable, value: ScriptValue) {
        match value {
            ScriptValue::Scalar(scalar) => self.update_local_scalar(var, scalar),
            ScriptValue::Function(sig) => self.update_local_function(var, sig),
            ScriptValue::Object(scope) => self.update_local_object(var, scope),
        }
    }

    pub fn update_global(&mut self, var: &Variable, value: ScriptValue) {
        match value {
            ScriptValue::Scalar(scalar) => self.update_global_scalar(var, scalar),
            ScriptValue::Function(sig) => self.update_global_function(var, sig),
            ScriptValue::Object(scope) => self.update_global_object(var, scope),
        }
    }

    pub fn update(&mut self, var: &Variable, is_global: bool, value: ScriptValue) {
        if is_global {
            self.update_global(var, value)
        } else {
            self.update_local(var, value)
        }
    }
}

pub(super) trait ScopeExt {
    fn new_child(&self) -> SharedScope;

    fn define(&mut self, var: &Variable, is_global: bool, value: ScriptValue);
}

impl ScopeExt for SharedScope {
    fn new_child(&self) -> SharedScope {
        Scope::new(Some(Rc::clone(self)))
    }

    fn define(&mut self, var: &Variable, is_global: bool, value: ScriptValue) {
        let (object, name) = if is_global {
            Scope::get_object_for_attribute_global(self, var)
        } else {
            Scope::get_object_for_attribute_local(self, var)
        };

        object.borrow_mut().add(name, value);
    }
}
