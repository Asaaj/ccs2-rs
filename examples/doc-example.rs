use ccs2::{CcsError, Context, ToType};
use env_logger::Builder;
use log::LevelFilter;

fn main() -> Result<(), CcsError> {
    Builder::new()
        .filter_level(LevelFilter::Info)
        .target(env_logger::Target::Stdout)
        .init();

    let context = Context::logging("examples/configs/doc.ccs", log::Level::Info)?;

    let constrained = context.constrain("a").constrain("c").constrain("d");
    assert_eq!(&constrained.get_type::<String>("x")?, "y");
    assert!(constrained.get("foobar").is_err());

    // Original context is untouched:
    assert_eq!(context.get("x")?.to_type::<i32>()?, 42);

    Ok::<(), ccs2::CcsError>(())
}
