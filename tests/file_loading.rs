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
    fn trace(&self, name: &str, value: &PropertyValue, context: DisplayContext) {
        eprintln!(
            "Found property: {name} = {}\n\t{context}\n\torigin: {}",
            value.value, value.origin
        );
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
