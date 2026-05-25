use binrw::binrw;
use bytemuck::Zeroable;
use num_traits::PrimInt;

pub trait GameConstant<I: PrimInt, const N: usize>: From<I> + Copy {
    fn all_values() -> [Self; N] {
        let mut values = [Self::from(I::zero()); N];
        let mut i = I::one();
        for value in &mut values {
            *value = Self::from(i);
            i = i
                .checked_add(&I::one())
                .expect("constant count N is too large for the constant type");
        }
        values
    }

    fn value(&self) -> I;

    fn constant_name(&self) -> Option<&'static str>;

    fn display_name(&self) -> &str {
        self.constant_name().unwrap_or("Unknown")
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct Difficulty(i32);

impl GameConstant<i32, 3> for Difficulty {
    fn value(&self) -> i32 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        None
    }

    fn display_name(&self) -> &str {
        match self.0 {
            0 => "Easy",
            1 => "Normal",
            2 => "Hard",
            _ => "Unknown",
        }
    }
}

impl From<i32> for Difficulty {
    fn from(value: i32) -> Self {
        Self(value)
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct Footing(i8);

impl Footing {
    pub const fn new(value: i8) -> Self {
        Self(value)
    }
}

impl GameConstant<i8, 7> for Footing {
    fn value(&self) -> i8 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        Some(match self.0 {
            0 => "FOOTING_KURONAMA",
            1 => "FOOTING_AKADAMA",
            2 => "FOOTING_SHUKUBA",
            3 => "FOOTING_SEIHU",
            4 => "FOOTING_NORMAL",
            5 => "FOOTING_EVENT",
            6 => "FOOTING_PLAYER",
            _ => return None,
        })
    }

    fn display_name(&self) -> &str {
        match self.0 {
            0 => "Kurou",
            1 => "Akadama",
            2 => "Station",
            3 => "Government",
            4 => "Normal",
            5 => "Event",
            6 => "Player",
            _ => "Unknown",
        }
    }
}

impl From<i8> for Footing {
    fn from(value: i8) -> Self {
        Self(value)
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct Map(i8);

impl GameConstant<i8, 15> for Map {
    fn all_values() -> [Self; 15] {
        [
            Self(0),
            Self(1),
            Self(2),
            Self(3),
            Self(4),
            Self(5),
            Self(6),
            Self(7),
            Self(24),
            Self(25),
            Self(26),
            Self(27),
            Self(28),
            Self(29),
            Self(30),
        ]
    }

    fn value(&self) -> i8 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        Some(match self.0 {
            0 => "MAPID_HASHI",
            1 => "MAPID_ZINZYA",
            2 => "MAPID_MATU",
            3 => "MAPID_YASHIKI",
            4 => "MAPID_SHUKUBA",
            5 => "MAPID_TETUDO",
            6 => "MAPID_YAKATA",
            7 => "MAPID_KOURO",
            24 => "MAPID_EVENTSHUKUBA",
            25 => "MAPID_BATTLE1",
            26 => "MAPID_BATTLE2",
            // the remaining 4 VS mode maps don't have associated constants
            _ => return None,
        })
    }

    fn display_name(&self) -> &str {
        match self.0 {
            0 => "Bridge",
            1 => "Shrine",
            2 => "Ipponmatsu",
            3 => "Kurou Residence",
            4 => "Station",
            5 => "Railroad",
            6 => "Akadama Clan Mansion",
            7 => "Iron Foundry",
            24 => "Station (event)",
            25 => "Arena",
            26 => "Plain",
            27 => "Water",
            28 => "Train",
            29 => "Metal Arena",
            30 => "Moon",
            _ => "Unknown",
        }
    }
}

impl From<i8> for Map {
    fn from(value: i8) -> Self {
        Self(value)
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct Time(i8);

impl GameConstant<i8, 3> for Time {
    fn value(&self) -> i8 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        Some(match self.0 {
            0 => "TIME_MORNING",
            1 => "TIME_AFTERNOON",
            2 => "TIME_EVENING",
            _ => return None,
        })
    }

    fn display_name(&self) -> &str {
        match self.0 {
            0 => "Morning",
            1 => "Afternoon",
            2 => "Evening",
            _ => "Unknown",
        }
    }
}

impl From<i8> for Time {
    fn from(value: i8) -> Self {
        Self(value)
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct AiStatus(u32);

impl GameConstant<u32, 16> for AiStatus {
    fn all_values() -> [Self; 16] {
        [
            Self(0),
            Self(1),
            Self(2),
            Self(3),
            Self(4),
            Self(5),
            Self(6),
            Self(7),
            Self(8),
            Self(9),
            Self(10),
            Self(11),
            Self(12),
            Self(13),
            Self(0x10000000),
            Self(0x40000000),
        ]
    }

    fn value(&self) -> u32 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        // this logic matches GetAIChar
        let ai_status = self.0 & 0xff7fffff;
        Some(match ai_status {
            0 | 0x80000000 => "AI_BATTLE",
            1 => "AI_NONCOM_IDLE",
            2 => "AI_CHASE",
            3 => "AI_APPROACH",
            4 => "AI_CATCH",
            5 => "AI_HOLD",
            6 => "AI_KICK",
            7 => "AI_RELCATCH",
            8 => "AI_RELHOLD",
            9 => "AI_MOVE",
            10 => "AI_TAKEUP",
            11 => "AI_CASTOFF",
            12 => "AI_RUGBY",
            13 => "AI_ANIMAL",
            0x10000000 => "AI_DEFENCE",
            0x40000000 => "AI_ESCORT",
            _ => return None,
        })
    }
}

impl From<u32> for AiStatus {
    fn from(value: u32) -> Self {
        Self(value)
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct CharacterId(i32);

impl CharacterId {
    pub const fn new(value: i32) -> Self {
        Self(value)
    }
}

impl GameConstant<i32, 103> for CharacterId {
    fn value(&self) -> i32 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        Some(match self.0 {
            0 => "CHID_SHUJINKO",
            1 => "CHID_TESHIN",
            2 => "CHID_SHIRETOKO",
            3 => "CHID_TUBOHACHI",
            4 => "CHID_MURASAKI",
            5 => "CHID_KICHO",
            6 => "CHID_CHELSEA",
            7 => "CHID_KARIBU",
            8 => "CHID_HYUGA",
            9 => "CHID_TOYOKO",
            10 => "CHID_SUZU",
            11 => "CHID_KURIKICHI",
            12 => "CHID_DONA",
            13 => "CHID_DOUJIMA",
            14 => "CHID_MOKICHI",
            15 => "CHID_HOSE",
            16 => "CHID_TAMAGAWA",
            17 => "CHID_COW",
            18 => "CHID_CAT",
            19 => "CHID_DOG",
            20 => "CHID_KUROZAKO1_0",
            21 => "CHID_KUROZAKO1_1",
            22 => "CHID_KUROZAKO1_2",
            23 => "CHID_KUROZAKO1_3",
            24 => "CHID_KUROZAKO1_4",
            25 => "CHID_KUROZAKO2_0",
            26 => "CHID_KUROZAKO2_1",
            27 => "CHID_KUROZAKO2_2",
            28 => "CHID_KUROZAKO2_3",
            29 => "CHID_KUROZAKO2_4",
            30 => "CHID_KUROZAKO3_0",
            31 => "CHID_KUROZAKO3_1",
            32 => "CHID_KUROZAKO3_2",
            33 => "CHID_KUROZAKO3_3",
            34 => "CHID_KUROZAKO3_4",
            35 => "CHID_KUROZAKO4_0",
            36 => "CHID_KUROZAKO4_1",
            37 => "CHID_KUROZAKO4_2",
            38 => "CHID_KUROZAKO4_3",
            39 => "CHID_KUROZAKO4_4",
            40 => "CHID_KUROZAKO5_0",
            41 => "CHID_KUROZAKO5_1",
            42 => "CHID_KUROZAKO5_2",
            43 => "CHID_KUROZAKO5_3",
            44 => "CHID_KUROZAKO5_4",
            45 => "CHID_KUROZAKO6_0",
            46 => "CHID_KUROZAKO6_1",
            47 => "CHID_KUROZAKO6_2",
            48 => "CHID_KUROZAKO6_3",
            49 => "CHID_KUROZAKO6_4",
            50 => "CHID_KUROZAKOUE_0",
            51 => "CHID_KUROZAKOUE_1",
            52 => "CHID_KUROZAKOUE_2",
            53 => "CHID_KUROZAKOUE_3",
            54 => "CHID_KUROZAKOUE_4",
            55 => "CHID_AKAZAKO1_0",
            56 => "CHID_AKAZAKO1_1",
            57 => "CHID_AKAZAKO1_2",
            58 => "CHID_AKAZAKO1_3",
            59 => "CHID_AKAZAKO1_4",
            60 => "CHID_AKAZAKO2_0",
            61 => "CHID_AKAZAKO2_1",
            62 => "CHID_AKAZAKO2_2",
            63 => "CHID_AKAZAKO2_3",
            64 => "CHID_AKAZAKO2_4",
            65 => "CHID_NINJA_0",
            66 => "CHID_NINJA_1",
            67 => "CHID_NINJA_2",
            68 => "CHID_NINJA_3",
            69 => "CHID_NINJA_4",
            70 => "CHID_NINJA_5",
            71 => "CHID_NINJA_6",
            72 => "CHID_NINJA_7",
            73 => "CHID_NINJA_8",
            74 => "CHID_NINJA_9",
            75 => "CHID_YAKUNIN_0",
            76 => "CHID_YAKUNIN_1",
            77 => "CHID_YAKUNIN_2",
            78 => "CHID_YAKUNIN_3",
            79 => "CHID_YAKUNIN_4",
            80 => "CHID_YAKUNIN_5",
            81 => "CHID_YAKUNIN_6",
            82 => "CHID_YAKUNIN_7",
            83 => "CHID_YAKUNIN_8",
            84 => "CHID_YAKUNIN_9",
            85 => "CHID_HOSEZAKO_0",
            86 => "CHID_HOSEZAKO_1",
            87 => "CHID_HOSEZAKO_2",
            88 => "CHID_HOSEZAKO_3",
            89 => "CHID_HOSEZAKO_4",
            90 => "CHID_HOSEZAKO_5",
            91 => "CHID_HOSEZAKO_6",
            92 => "CHID_HOSEZAKO_7",
            93 => "CHID_HOSEZAKO_8",
            94 => "CHID_HOSEZAKO_9",
            95 => "CHID_HYUGA2",
            96 => "CHID_SHUJINKO2",
            97 => "CHID_YAKUNIN_EX_0",
            98 => "CHID_YAKUNIN_EX_1",
            99 => "CHID_YAKUNIN_EX_2",
            100 => "CHID_YAKUNIN_EX_3",
            101 => "CHID_YAKUNIN_EX_4",
            102 => "CHID_COW2",
            _ => return None,
        })
    }

    fn display_name(&self) -> &str {
        match self.0 {
            -1 => "None",
            0 => "Player",
            1 => "Tesshin",
            2 => "Shiretoko",
            3 => "Tsubohachi",
            4 => "Murasaki",
            5 => "Kitcho",
            6 => "Chelsea",
            7 => "Karibu",
            8 => "Hyuga",
            9 => "Toyoko",
            10 => "Suzu",
            11 => "Kurikichi",
            12 => "Dona",
            13 => "Doujima",
            14 => "Inokashira",
            15 => "Hose",
            16 => "Tamagawa",
            17 => "Cow",
            18 => "Cat",
            19 => "Dog",
            20 => "Kurou Zako 1",
            21 => "Kurou Zako 1",
            22 => "Kurou Zako 1",
            23 => "Kurou Zako 1",
            24 => "Kurou Zako 1",
            25 => "Kurou Zako 2",
            26 => "Kurou Zako 2",
            27 => "Kurou Zako 2",
            28 => "Kurou Zako 2",
            29 => "Kurou Zako 2",
            30 => "Kurou Zako 3",
            31 => "Kurou Zako 3",
            32 => "Kurou Zako 3",
            33 => "Kurou Zako 3",
            34 => "Kurou Zako 3",
            35 => "Kurou Zako 4",
            36 => "Kurou Zako 4",
            37 => "Kurou Zako 4",
            38 => "Kurou Zako 4",
            39 => "Kurou Zako 4",
            40 => "Kurou Zako 5",
            41 => "Kurou Zako 5",
            42 => "Kurou Zako 5",
            43 => "Kurou Zako 5",
            44 => "Kurou Zako 5",
            45 => "Kurou Zako 6",
            46 => "Kurou Zako 6",
            47 => "Kurou Zako 6",
            48 => "Kurou Zako 6",
            49 => "Kurou Zako 6",
            50 => "Heavy Kurou Zako",
            51 => "Heavy Kurou Zako",
            52 => "Heavy Kurou Zako",
            53 => "Heavy Kurou Zako",
            54 => "Heavy Kurou Zako",
            55 => "Akadama Zako 1",
            56 => "Akadama Zako 1",
            57 => "Akadama Zako 1",
            58 => "Akadama Zako 1",
            59 => "Akadama Zako 1",
            60 => "Akadama Zako 2",
            61 => "Akadama Zako 2",
            62 => "Akadama Zako 2",
            63 => "Akadama Zako 2",
            64 => "Akadama Zako 2",
            65 => "Ninja",
            66 => "Ninja",
            67 => "Ninja",
            68 => "Ninja",
            69 => "Ninja",
            70 => "Ninja",
            71 => "Ninja",
            72 => "Ninja",
            73 => "Ninja",
            74 => "Ninja",
            75 => "Government Soldier",
            76 => "Government Soldier",
            77 => "Government Soldier",
            78 => "Government Soldier",
            79 => "Government Soldier",
            80 => "Government Soldier",
            81 => "Government Soldier",
            82 => "Government Soldier",
            83 => "Government Soldier",
            84 => "Government Soldier",
            85 => "Hose Zako",
            86 => "Hose Zako",
            87 => "Hose Zako",
            88 => "Hose Zako",
            89 => "Hose Zako",
            90 => "Hose Zako",
            91 => "Hose Zako",
            92 => "Hose Zako",
            93 => "Hose Zako",
            94 => "Hose Zako",
            95 => "Ninja Hyuga",
            96 => "Teacher",
            97 => "Heavy Government Soldier",
            98 => "Heavy Government Soldier",
            99 => "Heavy Government Soldier",
            100 => "Heavy Government Soldier",
            101 => "Heavy Government Soldier",
            102 => "Cow 2",
            _ => "Unknown",
        }
    }
}

impl From<i32> for CharacterId {
    fn from(value: i32) -> Self {
        Self(value)
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct Animation(i32);

impl GameConstant<i32, 363> for Animation {
    fn value(&self) -> i32 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        // high bits are used for flags
        let action_id = self.0 & 0xfff;
        Some(match action_id {
            0 => "MTAS_BASIC",
            1 => "MTAS_STOP",
            2 => "MTAS_E_STOP",
            3 => "MTAS_WALK",
            4 => "MTAS_BACK",
            5 => "MTAS_RUN",
            6 => "MTAS_JUMP",
            7 => "MTAS_LAND_A",
            8 => "MTAS_LAND_B",
            9 => "MTAS_FALL_A",
            10 => "MTAS_LADDER_A",
            11 => "MTAS_LADDER_B",
            12 => "MTAS_LADDER_C",
            13 => "MTAS_LADDER_D",
            14 => "MTAS_WAIT_R",
            15 => "MTAS_WAIT_L",
            16 => "MTAS_OPEN_R",
            17 => "MTAS_OPEN_L",
            18 => "MTAS_I_STOP",
            19 => "MTAS_EI_STOP",
            20 => "MTAS_I_RUN",
            21 => "MTAS_I_FALL",
            22 => "MTAS_I_LAND",
            23 => "MTAS_GET_A",
            24 => "MTAS_GET_B",
            25 => "MTAS_THROW_A",
            26 => "MTAS_THROW_B",
            27 => "MTAS_EAT",
            28 => "MTAS_SWING_A",
            29 => "MTAS_SWING_B",
            30 => "MTAS_GIVE",
            31 => "MTAS_TALK_A",
            32 => "MTAS_TALK_B",
            33 => "MTAS_TALK_C",
            34 => "MTAS_TALK_D",
            35 => "MTAS_TALK_E",
            36 => "MTAS_TALK_F",
            37 => "MTAS_TALK_G",
            38 => "MTAS_TALK_H",
            39 => "MTAS_TALK_I",
            40 => "MTAS_TALK_J",
            41 => "MTAS_TALK_K",
            42 => "MTAS_TALK_L",
            43 => "MTAS_TALK_M",
            44 => "MTAS_TALK_N",
            45 => "MTAS_SIT",
            46 => "MTAS_SIT_TALK_A",
            47 => "MTAS_SIT_TALK_B",
            48 => "MTAS_SIT_EAT",
            49 => "MTAS_SUWA_B",
            50 => "MTAS_TATU",
            51 => "MTAS_SLEEP_A",
            52 => "MTAS_KATU_S",
            53 => "MTAS_KATU_WALK",
            54 => "MTAS_KATU",
            55 => "MTAS_KATUG_S",
            56 => "MTAS_KATUG_A",
            57 => "MTAS_KATUG",
            58 => "MTAS_SUMAKI_A",
            59 => "MTAS_SUMAKI_B",
            60 => "MTAS_SUMAKI_C",
            61 => "MTAS_CAU",
            62 => "MTAS_KICK_A",
            63 => "MTAS_D_KICK_A",
            64 => "MTAS_J_KICK_A",
            65 => "MTAS_BOKO",
            66 => "MTAS_STG_A",
            67 => "MTAS_STG_B",
            68 => "MTAS_STG_C",
            69 => "MTAS_STG_D",
            70 => "MTAS_STG_E",
            71 => "MTAS_STG_F",
            72 => "MTAS_STG_G",
            73 => "MTAS_STG_H",
            74 => "MTAS_STG_I",
            75 => "MTAS_STG_J",
            76 => "MTAS_STG_K",
            77 => "MTAS_STG_L",
            78 => "MTAS_STG_M",
            79 => "MTAS_DRAW_A",
            80 => "MTAS_DRAW_B",
            81 => "MTAS_SHEATHE_B",
            82 => "MTAS_DRAW_G",
            83 => "MTAS_SHEATHE_G",
            84 => "MTAS_DRAW_R",
            85 => "MTAS_SHEATHE_R",
            86 => "MTAS_FALL_B",
            87 => "MTAS_FALL_C",
            88 => "MTAS_F_FATAL_A",
            89 => "MTAS_F_FATAL_C",
            90 => "MTAS_B_FATAL_A",
            91 => "MTAS_B_FATAL_B",
            92 => "MTAS_BLOW_F",
            93 => "MTAS_BLOW_B",
            94 => "MTAS_S_BLOW_F",
            95 => "MTAS_S_BLOW_B",
            96 => "MTAS_ROLL",
            97 => "MTAS_BLOWEND_A",
            98 => "MTAS_BLOWEND_B",
            99 => "MTAS_DOWN_A",
            100 => "MTAS_DOWN_B",
            101 => "MTAS_DOWND_A",
            102 => "MTAS_DOWND_B",
            103 => "MTAS_STAND_A",
            104 => "MTAS_STAND_B",
            105 => "MTAS_UKEMI",
            106 => "MTAS_SKY_LOVE",
            107 => "MTAS_OSARERU",
            108 => "MTAS_HIKARERU",
            109 => "MTAS_TUMBLE_A",
            110 => "MTAS_TUMBLE_B",
            111 => "MTAS_TUMBLE_C",
            112 => "MTAS_TUMBLE_D",
            113 => "MTAS_TUMBLE_E",
            114 => "MTAS_DANGER_A",
            115 => "MTAS_DANGER_B",
            116 => "MTAS_DYING01",
            117 => "MTAS_DYING02",
            118 => "MTAS_DYING03",
            119 => "MTAS_DYING05",
            120 => "MTAS_DEAD01",
            121 => "MTAS_DEAD02",
            122 => "MTAS_DEAD03",
            123 => "MTAS_DEAD05",
            124 => "MTAS_DEAD09",
            125 => "MTAS_DEAD10",
            126 => "MTAS_DEAD_D01",
            127 => "MTAS_DEAD_D02",
            128 => "MTAS_DEAD_D03",
            129 => "MTAS_DEAD_D05",
            130 => "MTAS_DEAD_D09",
            131 => "MTAS_DEAD_D10",
            132 => "MTAS_NAGEDAM_B",
            133 => "MTAS_SP_DAM_A",
            134 => "MTAS_SP_DAM_B",
            135 => "MTAS_SP_DAM_C",
            136 => "MTAS_SP_DAM_D",
            137 => "MTAS_SP_DAM_E",
            138 => "MTAS_SP_DAM_H",
            139 => "MTAS_SP_DAM_J",
            140 => "MTAS_SP_DAM_K",
            141 => "MTAS_SP_DAM_L",
            142 => "MTAS_SP_DAM_M",
            143 => "MTAS_SP_DAM_N",
            144 => "MTAS_SP_DAM_O",
            145 => "MTAS_SP_DAM_P",
            146 => "MTAS_SP_DAM_Q",
            147 => "MTAS_SP_DAM_R",
            148 => "MTAS_WALK_F",
            149 => "MTAS_WALK_B",
            150 => "MTAS_WALK_R",
            151 => "MTAS_WALK_L",
            152 => "MTAS_STEP_F",
            153 => "MTAS_STEP_B",
            154 => "MTAS_STEP_R",
            155 => "MTAS_STEP_L",
            156 => "MTAS_AT1_A",
            157 => "MTAS_AT2_A",
            158 => "MTAS_AT3_A",
            159 => "MTAS_AT1_C",
            160 => "MTAS_AT2_C",
            161 => "MTAS_ZAT_A",
            162 => "MTAS_ZAT_C",
            163 => "MTAS_YAT_A",
            164 => "MTAS_YAT_C",
            165 => "MTAS_ZAT_AG",
            166 => "MTAS_AT1_AG",
            167 => "MTAS_AT2_AG",
            168 => "MTAS_AT3_AG",
            169 => "MTAS_YAT_AG",
            170 => "MTAS_ZAT_CG",
            171 => "MTAS_AT1_CG",
            172 => "MTAS_AT2_CG",
            173 => "MTAS_YAT_CG",
            174 => "MTAS_JAT_A",
            175 => "MTAS_D_KICK_B",
            176 => "MTAS_D_KICK_C",
            177 => "MTAS_SAT_A",
            178 => "MTAS_SAT_B",
            179 => "MTAS_UPPER_A",
            180 => "MTAS_UPPER_B",
            181 => "MTAS_UPPER_C",
            182 => "MTAS_UPPER_D",
            183 => "MTAS_UPPER_E",
            184 => "MTAS_UPPER_F",
            185 => "MTAS_UPPER_H",
            186 => "MTAS_TUKI_A",
            187 => "MTAS_TUKI_B",
            188 => "MTAS_TUKING_A",
            189 => "MTAS_TUKING_B",
            190 => "MTAS_TUKING_C",
            191 => "MTAS_TUKI_G",
            192 => "MTAS_TUKI_H",
            193 => "MTAS_TUKI_I",
            194 => "MTAS_TUKI_J",
            195 => "MTAS_SPIN_A",
            196 => "MTAS_SPIN_B",
            197 => "MTAS_SPIN_C",
            198 => "MTAS_SPIN_D",
            199 => "MTAS_SPIN_E",
            200 => "MTAS_SPIN_F",
            201 => "MTAS_SPIN_H",
            202 => "MTAS_NUKI_A",
            203 => "MTAS_NUKI_C",
            204 => "MTAS_TOBASHI_A",
            205 => "MTAS_KESA_A",
            206 => "MTAS_KESA_B",
            207 => "MTAS_MOON",
            208 => "MTAS_ROLLING",
            209 => "MTAS_SP_A",
            210 => "MTAS_SP_B",
            211 => "MTAS_SP_C",
            212 => "MTAS_SP_D",
            213 => "MTAS_SP_E",
            214 => "MTAS_YOBU_A",
            215 => "MTAS_S_JAT_A",
            216 => "MTAS_S_JAT_C",
            217 => "MTAS_NAGE_A",
            218 => "MTAS_NAGE_B",
            219 => "MTAS_PENI_A",
            220 => "MTAS_PENI_B",
            221 => "MTAS_MARA",
            222 => "MTAS_OTA_A",
            223 => "MTAS_GUARD",
            224 => "MTAS_BREAK_A",
            225 => "MTAS_BREAK_B",
            226 => "MTAS_BREAK_C",
            227 => "MTAS_BLOKING_A",
            228 => "MTAS_BLOKING_B",
            229 => "MTAS_OSU",
            230 => "MTAS_HIKU_R",
            231 => "MTAS_HIKU_L",
            232 => "MTAS_HIKU_RX",
            233 => "MTAS_HIKU_LX",
            234 => "MTAS_DRAW_C",
            235 => "MTAS_SHEATHE_A",
            236 => "MTAS_KICK_E",
            237 => "MTAS_KAJIYA_A",
            238 => "MTAS_KAJIYA_B",
            239 => "MTAS_KAJIYA_C",
            240 => "MTAS_TUKI_E",
            241 => "MTAS_JTOBASI_A",
            242 => "MTAS_DRAGON_A",
            243 => "MTAS_DRAGON_C",
            244 => "MTAS_DRAGON_D",
            245 => "MTAS_DENPU_A",
            246 => "MTAS_DENPU_B",
            247 => "MTAS_DENPU_C",
            248 => "MTAS_SEN_A",
            249 => "MTAS_SEN_B",
            250 => "MTAS_SEN_C",
            251 => "MTAS_OYAJI_A",
            252 => "MTAS_OYAJI_B",
            253 => "MTAS_OYAJI_C",
            254 => "MTAS_OYAJI_D",
            255 => "MTAS_OYAJI_E",
            256 => "MTAS_OYAJI_F",
            257 => "MTAS_OYAJI_G",
            258 => "MTAS_HIKI_A",
            259 => "MTAS_HIKI_B",
            260 => "MTAS_KIAI",
            261 => "MTAS_TOBI_A",
            262 => "MTAS_J_KICK_B",
            263 => "MTAS_TUKI_C",
            264 => "MTAS_HOKO_A",
            265 => "MTAS_HOKO_C",
            266 => "MTAS_HOKO_D",
            267 => "MTAS_HOKO_E",
            268 => "MTAS_HOKO_F",
            269 => "MTAS_HOKO_G",
            270 => "MTAS_TATAKI_A",
            271 => "MTAS_TATAKI_B",
            272 => "MTAS_KORO_A",
            273 => "MTAS_KORO_B",
            274 => "MTAS_ABISE_A",
            275 => "MTAS_AIKI",
            276 => "MTAS_NAGE_D",
            277 => "MTAS_NAGE_E",
            278 => "MTAS_HOSE",
            279 => "MTAS_TUBOSP_A",
            280 => "MTAS_TUBOSP_B",
            281 => "MTAS_TUBOSP_C",
            282 => "MTAS_KICK_B",
            283 => "MTAS_NUKI",
            284 => "MTAS_NUKI_B",
            285 => "MTAS_NAGI_A",
            286 => "MTAS_KAMA_A",
            287 => "MTAS_KAMA_B",
            288 => "MTAS_IAI_A",
            289 => "MTAS_IAI_B",
            290 => "MTAS_SHIRESP_A",
            291 => "MTAS_SHIRESP_B",
            292 => "MTAS_SHIRESP_C",
            293 => "MTAS_SHIRESP_D",
            294 => "MTAS_SHIRESP_E",
            295 => "MTAS_SP",
            296 => "MTAS_TOYOSP_A",
            297 => "MTAS_TOYOSP_B",
            298 => "MTAS_TOYOSP_C",
            299 => "MTAS_TOYOSP_E",
            300 => "MTAS_TOYOSP_F",
            301 => "MTAS_TOYOSP_G",
            302 => "MTAS_TUKA_A",
            303 => "MTAS_TUKA_B",
            304 => "MTAS_TUKA_C",
            305 => "MTAS_FU_A",
            306 => "MTAS_BACK_A",
            307 => "MTAS_HIEN_A",
            308 => "MTAS_HIEN_B",
            309 => "MTAS_HIEN_C",
            310 => "MTAS_HIEN_D",
            311 => "MTAS_LAND_EX",
            312 => "MTAS_TOTU_A",
            313 => "MTAS_KUNAI_A",
            314 => "MTAS_KUNAI_B",
            315 => "MTAS_HIEN_E",
            316 => "MTAS_MIRAGE_A",
            317 => "MTAS_MIRAGE_B",
            318 => "MTAS_MIRAGE_C",
            319 => "MTAS_MIRAGE_D",
            320 => "MTAS_AT3_B",
            321 => "MTAS_YAT_B",
            322 => "MTAS_AT3_BG",
            323 => "MTAS_YAT_BG",
            324 => "MTAS_UPPER_G",
            325 => "MTAS_TUKI_D",
            326 => "MTAS_TUKI_F",
            327 => "MTAS_SPIN_G",
            328 => "MTAS_SOKU_A",
            329 => "MTAS_SOKU_B",
            330 => "MTAS_SUMER_A",
            331 => "MTAS_SUMER_B",
            332 => "MTAS_MUSUKO_A",
            333 => "MTAS_MUSUKO_B",
            334 => "MTAS_MUSUKO_C",
            335 => "MTAS_MUSUKO_D",
            336 => "MTAS_MUSUKO_J",
            337 => "MTAS_CHERUSP_A",
            338 => "MTAS_CHERUSP_B",
            339 => "MTAS_GUN_A",
            340 => "MTAS_GUN_G",
            341 => "MTAS_GUN_H",
            342 => "MTAS_GUN_B",
            343 => "MTAS_GUN_C",
            344 => "MTAS_GUN_D",
            345 => "MTAS_GUN_E",
            346 => "MTAS_GUN_F",
            347 => "MTAS_SU_A",
            348 => "MTAS_SU_B",
            349 => "MTAS_SU_C",
            350 => "MTAS_IKA_A",
            351 => "MTAS_IKA_B",
            352 => "MTAS_KANA_A",
            353 => "MTAS_KANA_B",
            354 => "MTAS_KANA_C",
            355 => "MTAS_YORO_A",
            356 => "MTAS_YORO_B",
            357 => "MTAS_YORO_C",
            358 => "MTAS_ODO_A",
            359 => "MTAS_YARA_A",
            360 => "MTAS_YARA_B",
            361 => "MTAS_UTA_A",
            362 => "MTAS_UTA_B",
            _ => return None,
        })
    }
}

impl From<i32> for Animation {
    fn from(value: i32) -> Self {
        Animation(value)
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct ObjectId(i32);

impl ObjectId {
    pub const fn new(value: i32) -> Self {
        Self(value)
    }
}

impl GameConstant<i32, 75> for ObjectId {
    fn value(&self) -> i32 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        Some(match self.0 {
            0 => "OBJ_DAIKON",
            1 => "OBJ_ANDON",
            2 => "OBJ_AYU",
            3 => "OBJ_CYOUMIRYOU",
            4 => "OBJ_DONBURI",
            5 => "OBJ_FUSUMA_A",
            6 => "OBJ_FUSUMA_B",
            7 => "OBJ_FUTON_A",
            8 => "OBJ_FUTON_B",
            9 => "OBJ_HASHI",
            10 => "OBJ_HISYAKU",
            11 => "OBJ_HOUKI",
            12 => "OBJ_HYOUTAN",
            13 => "OBJ_ISU_A",
            14 => "OBJ_ISU_B",
            15 => "OBJ_ISU_C",
            16 => "OBJ_KAMA",
            17 => "OBJ_KAME",
            18 => "OBJ_KUWA",
            19 => "OBJ_MANEKINEKO",
            20 => "OBJ_MOKUHEN",
            21 => "OBJ_NABE",
            22 => "OBJ_OCYOKO",
            23 => "OBJ_OKE",
            24 => "OBJ_OSHINAGAKI",
            25 => "OBJ_OWAN",
            26 => "OBJ_SAISENBAKO",
            27 => "OBJ_SARA",
            28 => "OBJ_SHIKII",
            29 => "OBJ_SYAMOJI",
            30 => "OBJ_TOBIRA_A",
            31 => "OBJ_TOBIRA_B",
            32 => "OBJ_TOKURI",
            33 => "OBJ_TSUKUE",
            34 => "OBJ_TUBO",
            35 => "OBJ_TURIZAO",
            36 => "OBJ_ZABUTON_A",
            37 => "OBJ_ZABUTON_B",
            38 => "OBJ_ZORI_A",
            39 => "OBJ_SUMAKI",
            40 => "OBJ_BIRD",
            41 => "OBJ_KIBAKO",
            42 => "OBJ_AKAGO",
            43 => "OBJ_AMADO_A",
            44 => "OBJ_AMADO_B",
            45 => "OBJ_DOOR_A",
            46 => "OBJ_FUSUMA_C",
            47 => "OBJ_FUSUMA_D",
            48 => "OBJ_MONN_A",
            49 => "OBJ_SYOUJI_A",
            50 => "OBJ_SYOUJI_B",
            51 => "OBJ_KINKO",
            52 => "OBJ_UBAGURUMA",
            53 => "OBJ_UBAGURUMA_SET",
            54 => "OBJ_KISYA_A",
            55 => "OBJ_KISYA_B",
            56 => "OBJ_FUSUMA_E",
            57 => "OBJ_FUSUMA_F",
            58 => "OBJ_CARRY",
            59 => "OBJ_OMURICE",
            60 => "OBJ_TAIHOU",
            61 => "OBJ_BALL",
            62 => "OBJ_HIYOKO",
            63 => "OBJ_ABURA",
            64 => "OBJ_UTIKO",
            65 => "OBJ_OMAMORI",
            66 => "OBJ_OUGISHO",
            67 => "OBJ_MIKIRISHO",
            68 => "OBJ_OKANE1",
            69 => "OBJ_OKANE2",
            70 => "OBJ_KINOKO",
            71 => "OBJ_FUTON_C",
            72 => "OBJ_FUTON_D",
            73 => "OBJ_CHAIR",
            74 => "OBJ_USISAKI",
            _ => return None,
        })
    }

    fn display_name(&self) -> &str {
        match self.0 {
            -1 => "None",
            _ => self.constant_name().unwrap_or("Unknown"),
        }
    }
}

impl From<i32> for ObjectId {
    fn from(value: i32) -> Self {
        ObjectId(value)
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct Friend(i8);

impl Friend {
    pub const fn new(value: i8) -> Self {
        Self(value)
    }
}

impl GameConstant<i8, 4> for Friend {
    fn value(&self) -> i8 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        Some(match self.0 {
            0 => "FRIEND_NOMEET",
            1 => "FRIEND_MEET",
            2 => "FRIEND_FELLOW",
            3 => "FRIEND_ENEMY",
            _ => return None,
        })
    }

    fn display_name(&self) -> &str {
        match self.0 {
            0 => "Not met",
            1 => "Met",
            2 => "Ally",
            3 => "Enemy",
            _ => "Unknown",
        }
    }
}

impl From<i8> for Friend {
    fn from(value: i8) -> Self {
        Friend(value)
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct Watch(i32);

impl GameConstant<i32, 3> for Watch {
    fn value(&self) -> i32 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        Some(match self.0 {
            0 => "WATCH_LEAVE",
            1 => "WATCH_STOP",
            2 => "WATCH_OBJECT",
            _ => return None,
        })
    }

    fn display_name(&self) -> &str {
        match self.0 {
            0 => "Leave",
            1 => "Stop",
            2 => "Object",
            _ => "Unknown",
        }
    }
}

impl From<i32> for Watch {
    fn from(value: i32) -> Self {
        Watch(value)
    }
}

#[binrw]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Zeroable)]
#[repr(transparent)]
pub struct EventProgress(i8);

impl GameConstant<i8, 4> for EventProgress {
    fn value(&self) -> i8 {
        self.0
    }

    fn constant_name(&self) -> Option<&'static str> {
        Some(match self.0 {
            0 => "EVENTPRO_NULL",
            1 => "EVENTPRO_RETURN",
            2 => "EVENTPRO_STOP",
            3 => "EVENTPRO_END",
            _ => return None,
        })
    }

    fn display_name(&self) -> &str {
        match self.0 {
            0 => "Null",
            1 => "Return",
            2 => "Stop",
            3 => "End",
            _ => "Unknown",
        }
    }
}

impl From<i8> for EventProgress {
    fn from(value: i8) -> Self {
        EventProgress(value)
    }
}

/// For each `EVENT_` constant, indicates whether its bit (`1 << value`) is set in `modes`. The
/// returned entries are ordered by the constants' values, so index `i` corresponds to bit `i`.
pub(super) const fn event_modes(modes: u64) -> [(&'static str, bool); 15] {
    const EVENT_NAMES: [&str; 15] = [
        "EVENT_DAMAGE",
        "EVENT_COLL",
        "EVENT_TIMEOUT",
        "EVENT_TALK",
        "EVENT_THINK",
        "EVENT_WATCH",
        "EVENT_WEAPON_ON",
        "EVENT_WEAPON_OFF",
        "EVENT_BORDERLINE",
        "EVENT_POSBORDERLINE",
        "EVENT_DOWN",
        "EVENT_DEAD",
        "EVENT_LINEVIEW",
        "EVENT_MAPOUT",
        "EVENT_AI",
    ];

    let mut result = [("", false); 15];
    let mut i = 0;
    while i < result.len() {
        result[i] = (EVENT_NAMES[i], modes & (1 << i) != 0);
        i += 1;
    }
    result
}
