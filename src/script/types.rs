use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::ops::Deref;
use std::rc::{Rc, Weak};
use std::str::FromStr;

use anyhow::{anyhow, Error};
use common_macros::hash_map;
use lazy_static::lazy_static;
use strum::{EnumIter, EnumString};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, EnumString, EnumIter)]
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
    // these don't follow the normal naming convention and need special handling
    Boolean,
    Relation,
    FadeDir,
    FadeType,
    Initialize,
    Null,
    Any,               // any other type not identified above
    Select,            // select the type of a following argument
    SendFuncCharacter, // either a character ID or null depending on the previous select arg
    Conflict, // we've detected multiple conflicting types for this value and should treat it as an unknown type
}

impl Default for EnumType {
    fn default() -> Self {
        Self::Any
    }
}

impl EnumType {
    pub fn is_concrete(&self) -> bool {
        !matches!(self, Self::Any | Self::Conflict) && !self.is_select()
    }

    pub fn is_select(&self) -> bool {
        matches!(self, Self::Select | Self::SendFuncCharacter)
    }

    /// Choose the more specific of this type and another type
    ///
    /// If the level of specificity is the same, the other type is preferred.
    pub fn choose(&self, other: Self) -> Self {
        if *self == Self::Conflict || (self.is_concrete() && other.is_concrete() && *self != other)
        {
            Self::Conflict
        } else if other == Self::Any
            || (self.is_concrete() && !other.is_concrete())
            || (self.is_select() && !other.is_concrete())
        {
            *self
        } else {
            other
        }
    }

    pub fn select_type(&self, select_value: Option<i32>) -> Self {
        match self {
            Self::SendFuncCharacter => match select_value {
                None => Self::Any,
                Some(1) => Self::Null,
                _ => Self::Character,
            },
            _ if !self.is_concrete() => Self::Any,
            _ => *self,
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

lazy_static! {
    static ref SIGNATURES: HashMap<&'static str, Signature> = hash_map! {
        "DelAIChar" => Signature::args(vec![EnumType::Character]),
        "SetAIChar" => Signature::args(vec![EnumType::Character, EnumType::Ai]),
        "GetAIChar" => Signature::args(vec![EnumType::Character]),
        "SetAITargetItem" => Signature::args(vec![EnumType::Character, EnumType::Object]),
        "SetCharPos" => Signature::args(vec![EnumType::Character]),
        "SetCharDir" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "SetCharDir2" => Signature::args(vec![EnumType::Character]),
        "SetAIBackLimit" => Signature::args(vec![EnumType::Character]),
        "SetAIWalkLimit" => Signature::args(vec![EnumType::Character]),
        "SetAISiegeLimit" => Signature::args(vec![EnumType::Character]),
        "SetAIRunLimit" => Signature::args(vec![EnumType::Character]),
        "SetSoloCamera" => Signature::args(vec![EnumType::Character]),
        "SetFixCamera" => Signature::args(vec![EnumType::Character]),
        "Say" => Signature::args(vec![EnumType::Character, EnumType::Character, EnumType::Any, EnumType::Any, EnumType::Any, EnumType::Say]),
        "SetSayMotion" => Signature::args(vec![EnumType::Character, EnumType::Command]),
        "SetTalkSelect" => Signature::args(vec![EnumType::Character]),
        "SetTimeAction" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "SetCharAction" => Signature::args(vec![EnumType::Character, EnumType::Command]),
        "SetAICharMove" => Signature::args(vec![EnumType::Character, EnumType::Command]),
        "SetEventMode" => Signature::args(vec![EnumType::Character]).vararg(EnumType::Event),
        "SubEventMode" => Signature::args(vec![EnumType::Character]).vararg(EnumType::Event),
        "GetCharPos" => Signature::args(vec![EnumType::Character]),
        "SetCharDraw" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "AddSamuraiValue" => Signature::args(vec![EnumType::Character]),
        "SubSamuraiValue" => Signature::args(vec![EnumType::Character]),
        "SetLineAction" => Signature::args(vec![EnumType::Character]),
        "SetMapID" => Signature::args(vec![EnumType::Map]),
        "SetCharLevel" => Signature::args(vec![EnumType::Character]),
        "SetEventUseCharList" => Signature::varargs(EnumType::Character),
        "SetCharDrawOnList" => Signature::varargs(EnumType::Character),
        "SetCharDrawOffList" => Signature::varargs(EnumType::Character),
        "SetAddCharScript" => Signature::args(vec![EnumType::Character]),
        "SetCharNoCollMode" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SetAIGroupRelation" => Signature::args(vec![EnumType::Footing, EnumType::Footing, EnumType::Relation]),
        "SendFunc" => Signature::args(vec![EnumType::Select, EnumType::SendFuncCharacter]),
        "SendFunc2" => Signature::args(vec![EnumType::Select, EnumType::SendFuncCharacter]),
        "SetAddCharScriptList" => Signature::args(vec![EnumType::Any]).vararg(EnumType::Character),
        "SetCharNeckAction" => Signature::args(vec![EnumType::Character]),
        "SetCharFace" => Signature::args(vec![EnumType::Character, EnumType::Animation]),
        "SetObjDraw" => Signature::args(vec![EnumType::Object, EnumType::Boolean]),
        "SetCharGroupID" => Signature::args(vec![EnumType::Character, EnumType::Footing]),
        "SetCharLife" => Signature::args(vec![EnumType::Character]),
        "SetCharHiFaceMode" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SetPosLineAction" => Signature::args(vec![EnumType::Character]),
        "SetAIAllStop" => Signature::args(vec![EnumType::Boolean]),
        "SetCharForm" => Signature::args(vec![EnumType::Character]),
        "SetCutCamera" => Signature::args(vec![EnumType::Camera]),
        "SetCharFriendFlag" => Signature::args(vec![EnumType::Character, EnumType::Friend]),
        "SetCameraPos" => Signature::args(vec![EnumType::Camera]),
        "SetSayPos" => Signature::args(vec![EnumType::Character]),
        "SetCharMove" => Signature::args(vec![EnumType::Character, EnumType::Command]),
        "SetCharShowList" => Signature::args(vec![EnumType::Boolean]).vararg(EnumType::Character),
        "SetCharTarget" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "GetCharDead" => Signature::args(vec![EnumType::Character]),
        "SetMapTimeID" => Signature::args(vec![EnumType::Time]),
        "SetCharWatch" => Signature::args(vec![EnumType::Character]),
        "SetCharPosFixMode" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "SetObjMoveTetudo" => Signature::args(vec![EnumType::Boolean]),
        "SetCharNoDamageMode" => Signature::args(vec![EnumType::Character, EnumType::Boolean]),
        "ScreenEffect" => Signature::args(vec![EnumType::Effect, EnumType::FadeDir, EnumType::FadeType]),
        "SetEventProFlag" => Signature::args(vec![EnumType::Any, EnumType::EventProgress]),
        "VoicePlay" => Signature::args(vec![EnumType::Any, EnumType::Any, EnumType::Character]),
        "StartCharTrace" => Signature::args(vec![EnumType::Character, EnumType::Character, EnumType::Command]),
        "SetPadMode" => Signature::args(vec![EnumType::Boolean]),
        "SetObjAction" => Signature::args(vec![EnumType::Object]),
        "GetCharThrowCount" => Signature::args(vec![EnumType::Character]),
        "GetCharStatus" => Signature::args(vec![EnumType::Character, EnumType::Event]),
        "AddCharDaikonFlag" => Signature::args(vec![EnumType::Character]),
        "SubCharDaikonFlag" => Signature::args(vec![EnumType::Character]),
        "GetObjChar" => Signature::args(vec![EnumType::Character]),
        "ClearFrontEvent" => Signature::args(vec![EnumType::Character]),
        "GetDamageKind" => Signature::args(vec![EnumType::Character]).returns(EnumType::Damage),
        "AddEventMode" => Signature::args(vec![EnumType::Character]).vararg(EnumType::Event),
        "SetCharWaiting" => Signature::args(vec![EnumType::Character]),
        "SetCharDeathBlow" => Signature::args(vec![EnumType::Character]),
        "StopCharTrace" => Signature::args(vec![EnumType::Character]),
        "GetCharFriendFlag" => Signature::args(vec![EnumType::Character]).returns(EnumType::Friend),
        "GetCharRange" => Signature::args(vec![EnumType::Character]),
        "GetEventProFlag" => Signature::args(vec![EnumType::Any]).returns(EnumType::EventProgress),
        // callback functions
        "MapIn" => Signature::args(vec![EnumType::Map]),
        "MapOut" => Signature::args(vec![EnumType::Map]),
        "Collision" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "Damage" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "TalkEnd" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "TalkSelect" => Signature::args(vec![EnumType::Character]),
        "PosJoin" => Signature::args(vec![EnumType::Character]),
        "PosLeave" => Signature::args(vec![EnumType::Character]),
        "Join" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "Leave" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "TimeOut" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "SayDead" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "NpcOut" => Signature::args(vec![EnumType::Character]),
        "WeaponOn" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "WeaponOff" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "Dead" => Signature::args(vec![EnumType::Character, EnumType::Character]),
        "Watch" => Signature::args(vec![EnumType::Character, EnumType::Character]),
    };
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub(super) struct Signature {
    arguments: Vec<EnumType>,
    vararg: EnumType,
    return_type: EnumType,
}

impl Signature {
    pub fn args(arguments: Vec<EnumType>) -> Self {
        Self {
            arguments,
            vararg: EnumType::default(),
            return_type: EnumType::default(),
        }
    }

    pub fn varargs(arg_type: EnumType) -> Self {
        Self {
            arguments: vec![],
            vararg: arg_type,
            return_type: EnumType::default(),
        }
    }

    pub fn vararg(mut self, arg_type: EnumType) -> Self {
        self.vararg = arg_type;
        self
    }

    pub fn returns(mut self, return_type: EnumType) -> Self {
        self.return_type = return_type;
        self
    }

    pub fn get_argument(&self, index: usize) -> EnumType {
        self.arguments.get(index).copied().unwrap_or_default()
    }

    pub fn add_argument(&mut self, index: usize, arg_type: EnumType) -> EnumType {
        if index >= self.arguments.len() {
            self.arguments.resize_with(index + 1, Default::default);
        }
        self.arguments[index].update(arg_type)
    }

    pub fn iter(&self) -> impl Iterator<Item = EnumType> + '_ {
        self.arguments
            .iter()
            .copied()
            .chain(std::iter::repeat(self.vararg))
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
        for (our_arg, &their_arg) in self.arguments.iter_mut().zip(other.arguments.iter()) {
            our_arg.update(their_arg);
        }
        if other.arguments.len() > self.arguments.len() {
            self.arguments
                .extend_from_slice(&other.arguments[self.arguments.len()..]);
        }
        self.vararg.update(other.vararg);
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

    fn lookup_scalar_local(&self, name: &str) -> Option<EnumType> {
        self.lookup_own_scalar(name)
            .or_else(|| parent!(self, lookup_scalar_local(name)))
    }

    fn lookup_scalar_global(&self, name: &str) -> Option<EnumType> {
        parent!(self, lookup_scalar_global(name)).or_else(|| self.lookup_own_scalar(name))
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

    pub fn lookup_scalar_attribute(&self, var: &Variable) -> Option<EnumType> {
        match var {
            Variable(name, None) => self.lookup_own_scalar(name),
            Variable(name, Some(attr)) => self
                .lookup_own_object(name)
                .and_then(|o| o.borrow().lookup_scalar_attribute(attr.as_ref())),
        }
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

    pub fn lookup_local_scalar(&self, var: &Variable) -> EnumType {
        match var {
            Variable(name, None) => self.lookup_scalar_local(name),
            Variable(name, Some(attr)) => self
                .lookup_object_local(name)
                .and_then(|o| o.borrow().lookup_scalar_attribute(attr.as_ref())),
        }
        .unwrap_or_default()
    }

    pub fn lookup_global_scalar(&self, var: &Variable) -> EnumType {
        match var {
            Variable(name, None) => self.lookup_scalar_global(name),
            Variable(name, Some(attr)) => self
                .lookup_object_global(name)
                .and_then(|o| o.borrow().lookup_scalar_attribute(attr.as_ref())),
        }
        .unwrap_or_default()
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

    pub fn lookup_scalar(&self, var: &Variable, is_global: bool) -> EnumType {
        if is_global {
            self.lookup_global_scalar(var)
        } else {
            self.lookup_local_scalar(var)
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
