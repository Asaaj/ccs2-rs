use crate::{PersistentStr, PropertyValue, ast::Origin};

/// Occurs when parsing a string into a specific type fails
///
/// Created when converting a [`PropertyValue`] with [`ToType::to_type`]
#[derive(thiserror::Error, Debug)]
#[error("Conversion to {type_name} failed for value {value} ({origin})")]
pub struct ConversionFailed {
    pub type_name: &'static str,
    pub value: PersistentStr,
    pub origin: Origin,
}

pub type ConversionResult<T> = Result<T, ConversionFailed>;

/// Represents a type which can be created from a [`PropertyValue`]
///
/// `TypedProperty` can be implemented for user-defined types to make it more convenient to parse
/// things. However, if you want to implement it for types that aren't defined in your crate, you'll
/// have to use a newtype.
///
/// Example:
///
/// ```
/// use ccs2::{CommaSeparatedList, ToType};
/// let context = ccs2::Context::new("items = '1, 2, 3, 4'", ccs2::NullTracer {}).unwrap();
///
/// let items = context.get_type::<CommaSeparatedList>("items")?;
///
/// assert_eq!(items.0, vec!["1", "2", "3", "4"]);
/// # Ok::<(), ccs2::ContextError>(())
/// ```
///
/// Note: The combined error type of the "get and convert" chain is [`ContextError`].
///
/// [`ContextError`]: crate::ContextError
pub trait TypedProperty {
    fn from_value(value: &PropertyValue) -> ConversionResult<Self>
    where
        Self: Sized;
}

/// A helper trait implemented by [`PropertyValue`] to make string parsing/conversion easier
///
/// See implementers of [`TypedProperty`] for more
pub trait ToType {
    fn to_type<T: TypedProperty>(&self) -> ConversionResult<T>
    where
        Self: Sized;
}
impl ToType for PropertyValue {
    fn to_type<T: TypedProperty>(&self) -> ConversionResult<T> {
        T::from_value(self)
    }
}

impl TypedProperty for bool {
    fn from_value(prop: &PropertyValue) -> ConversionResult<Self> {
        prop.value.parse::<bool>().or_conversion_failed(prop)
    }
}

impl TypedProperty for String {
    fn from_value(prop: &PropertyValue) -> ConversionResult<Self> {
        Ok(prop.value.to_string())
    }
}

impl TypedProperty for std::path::PathBuf {
    fn from_value(prop: &PropertyValue) -> ConversionResult<Self> {
        Ok(std::path::PathBuf::from(prop.value.as_ref()))
    }
}

/// Splits at commas, and trims whitespace from both ends of resulting items
///
/// TODO: Would be nice to make this trait lifetime-aware, so we could do `Vec<&str>`
#[derive(Debug)]
pub struct CommaSeparatedList(pub Vec<String>);
impl TypedProperty for CommaSeparatedList {
    fn from_value(prop: &PropertyValue) -> ConversionResult<Self> {
        Ok(CommaSeparatedList(
            prop.value
                .as_ref()
                .split(",")
                .map(|s| s.trim().to_string())
                .collect(),
        ))
    }
}

macro_rules! num_type {
    ($num:ty) => {
        impl TypedProperty for $num {
            fn from_value(prop: &PropertyValue) -> ConversionResult<Self> {
                prop.value.parse::<$num>().or_conversion_failed(prop)
            }
        }
    };
}

num_type!(i8);
num_type!(u8);

num_type!(i16);
num_type!(u16);

num_type!(i32);
num_type!(u32);
num_type!(f32);

num_type!(i64);
num_type!(u64);
num_type!(f64);

#[cfg(feature = "extra_conversions")]
pub mod extras {
    use super::*;

    /// Requires the `extra_conversions` feature, as it uses [`humantime`] crate to do the parsing
    impl TypedProperty for std::time::Duration {
        fn from_value(prop: &PropertyValue) -> ConversionResult<Self> {
            humantime::parse_duration(prop.value.as_ref()).or_conversion_failed(prop)
        }
    }
}

/// Helper to make the conversion errors easier to spell
pub trait OrConversionFailed<T: TypedProperty> {
    fn or_conversion_failed(self, original: &PropertyValue) -> ConversionResult<T>;
}
impl<T: TypedProperty, E> OrConversionFailed<T> for std::result::Result<T, E> {
    fn or_conversion_failed(self, original: &PropertyValue) -> ConversionResult<T> {
        match self {
            Ok(value) => Ok(value),
            Err(_) => Err(ConversionFailed {
                type_name: simple_type_name::<T>().unwrap_or("UNKNOWN"),
                value: original.value.clone(),
                origin: original.origin.clone(),
            }),
        }
    }
}

fn simple_type_name<T>() -> Option<&'static str> {
    std::any::type_name::<T>().split("::").last()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CcsResult, Context};
    use assert_approx_eq::assert_approx_eq;
    use std::time::Duration;

    #[test]
    fn get_duration() -> CcsResult<()> {
        let contents = r#"
        duration1 = '5ms'
        duration2 = '3h'
        constrained { duration2 = '1d5h' }
        "#;
        let context = Context::without_tracing(contents)?;

        assert_eq!(
            context.get("duration1")?.to_type::<Duration>()?,
            Duration::from_millis(5)
        );
        assert_eq!(
            context.get("duration2")?.to_type::<Duration>()?,
            Duration::from_hours(3)
        );

        let context = context.constrain("constrained");
        assert_eq!(
            context.get("duration2")?.to_type::<Duration>()?,
            Duration::from_hours(29)
        );

        Ok(())
    }

    #[test]
    fn get_comma_separated_list() -> CcsResult<()> {
        let contents = r#"
        oneLineList = "first, second   ,third"
        multiLineList = "
            this,
            that,
            the other,
        " // Extra comma will make an empty element
        "#;
        let context = Context::without_tracing(contents)?;

        assert_eq!(
            context
                .get("oneLineList")?
                .to_type::<CommaSeparatedList>()?
                .0,
            ["first", "second", "third"]
        );

        assert_eq!(
            context
                .get("multiLineList")?
                .to_type::<CommaSeparatedList>()?
                .0,
            ["this", "that", "the other", ""]
        );

        Ok(())
    }

    #[test]
    fn get_arithmetic_types() -> CcsResult<()> {
        let contents = r#"
        boolVal = false
        intVal = 123
        floatVal = 123.4
        "#;
        let context = Context::without_tracing(contents)?;

        let bool_val = context.get("boolVal")?;
        let int_val = context.get("intVal")?;
        let float_val = context.get("floatVal")?;

        assert!(!(bool_val.to_type::<bool>()?));

        assert_eq!(int_val.to_type::<u32>()?, 123u32);
        assert_eq!(int_val.to_type::<i64>()?, 123i64);

        assert_approx_eq!(float_val.to_type::<f32>()?, 123.4f32);
        assert_approx_eq!(float_val.to_type::<f64>()?, 123.4f64);

        Ok(())
    }

    #[test]
    fn realistic_constraints() -> CcsResult<()> {
        let contents = r#"
            env.prod module.logger {
                level = INFO
            }
            env.dev module.logger {
                level = DEBUG
            }
            env.dev module.debug {
                format = "example format"
            }
        "#;
        let context = Context::without_tracing(contents)?;

        let prod_logger = context
            .constrain(("env", "prod"))
            .constrain(("module", "logger"));
        let dev_logger = context
            .constrain(("env", "dev"))
            .constrain(("module", "logger"));

        assert_eq!(&*prod_logger.get_value("level")?, "INFO");
        assert_eq!(&*dev_logger.get_value("level")?, "DEBUG");

        let dev_debug_module = context
            .constrain(("env", "dev"))
            .constrain(("module", "debug"));

        assert_eq!(&*dev_debug_module.get_value("format")?, "example format");
        assert!(dev_debug_module.get_value("level").is_err());

        Ok(())
    }
}
