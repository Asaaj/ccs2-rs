use std::path::{Path, PathBuf};

use ccs2::*;

fn resolve_example(example_path: impl AsRef<Path>) -> PathBuf {
    let cwd = std::env::current_dir().expect("Failed to get working directory; can't load files");
    if !(cwd.join("tests")).is_dir() {
        panic!("Unknown working directory: {cwd:?}");
    }

    cwd.join("tests").join(example_path.as_ref())
}

#[derive(Copy, Clone)]
struct EPrintTracer();
impl PropertyTracer for EPrintTracer {
    fn on_found(&self, name: &str, value: &PropertyValue, context: DisplayContext) {
        eprintln!(
            "Found property: {name} = {}\n\t{context}\n\torigin: {}",
            value.value, value.origin
        );
    }

    fn on_error(&self, error: SearchError) {
        match error {
            SearchError::MissingPropertyError { name, context } => {
                eprintln!("Property not found: {name}\n\t{context}");
            }
            SearchError::EmptyPropertyError { name, context } => {
                eprintln!("Empty property found: {name}\n\t{context}");
            }
            SearchError::AmbiguousPropertyError {
                count,
                name,
                context,
            } => {
                eprintln!("Ambiguous property found ({count} values): {name}\n\t{context}");
            }
        }
    }
}

#[test]
fn single_level_import() -> CcsResult<()> {
    let context = Context::load_with_tracer(
        resolve_example("configs/imports/single_level.ccs"),
        EPrintTracer(),
    )?;

    assert!(context.get("x").is_err());

    let context = context.constrain("multi");
    assert_eq!(&*context.get_value("x")?, "failure");

    let context = context.constrain("level");
    assert_eq!(&*context.get_value("x")?, "success");

    Ok(())
}

#[test]
fn multi_level_import() -> CcsResult<()> {
    let context = Context::load_with_tracer(
        resolve_example("configs/imports/multi_level.ccs"),
        EPrintTracer(),
    )?;

    assert!(context.get("x").is_err());

    let context = context.constrain(("outermost", "level")).constrain("multi");
    assert_eq!(&*context.get_value("x")?, "failure");

    let context = context.constrain("level");
    assert_eq!(&*context.get_value("x")?, "success");

    Ok(())
}

#[test]
fn circular_import() -> CcsResult<()> {
    assert!(
        Context::load_with_tracer(
            resolve_example("configs/imports/circular1.ccs"),
            EPrintTracer()
        )
        .is_err_and(|e| format!("{e}").contains("circular2.ccs"))
    );
    Ok(())
}

#[test]
fn imported_multiple_times() -> CcsResult<()> {
    let context = Context::load_with_tracer(
        resolve_example("configs/imports/multiple_times.ccs"),
        EPrintTracer(),
    )?;

    assert!(context.get("x").is_err());

    let context1 = context.constrain("context1");
    assert_eq!(&*context1.get_value("x")?, "success");

    let context2 = context.constrain("context2");
    assert_eq!(&*context2.get_value("x")?, "success");

    let context3 = context.constrain("context3");
    assert_eq!(&*context3.get_value("x")?, "success");

    Ok(())
}

#[test]
fn subdirectories_are_relative_to_importer() -> CcsResult<()> {
    let context = Context::load_with_tracer(
        resolve_example("configs/imports/imports_directory.ccs"),
        EPrintTracer(),
    )?;

    assert_eq!(context.constrain("outercontext").get_type::<i32>("x")?, 42);
    Ok(())
}
