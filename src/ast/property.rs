use std::fmt::Display;

use crate::ast::{Origin, PersistentStr, PropDef};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PropertyValue {
    pub value: PersistentStr,
    pub origin: Origin,
    pub override_level: u32,
}
impl PropertyValue {
    pub fn new(value: impl ToString, origin: Origin, override_level: u32) -> Self {
        Self {
            value: value.to_string().into(),
            origin,
            override_level,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Property(pub PersistentStr, pub PropertyValue);

impl Property {
    pub fn new(
        name: impl ToString,
        value: impl ToString,
        origin: Origin,
        should_override: bool,
    ) -> Self {
        Self(
            name.to_string().into(),
            PropertyValue::new(value, origin, if should_override { 1 } else { 0 }),
        )
    }
}

impl From<PropDef> for Property {
    fn from(def: PropDef) -> Self {
        Self::new(def.name, def.value, def.origin, def.should_override)
    }
}
impl Display for Property {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.0, self.1.value)
    }
}
