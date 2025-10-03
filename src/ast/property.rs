use crate::ast::Origin;

#[derive(Clone, Debug)]
pub struct Property {
    value: String,
    origin: Origin,
    override_level: u32,
}
impl Property {
    pub fn new(value: impl ToString, origin: Origin, override_level: u32) -> Self {
        Self {
            value: value.to_string(),
            origin,
            override_level,
        }
    }
}
