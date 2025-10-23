use ccs2::{CcsError, Context, ToType};
use env_logger::Builder;
use log::LevelFilter;

fn main() -> Result<(), CcsError> {
    Builder::new()
        .filter_level(LevelFilter::Info)
        .target(env_logger::Target::Stdout)
        .init();

    // Usually from a file
    let ccs_str = r#"
        a, f b e, c {
            c d {
                x = y
            }
            e f {
                foobar = abc
            }
        }

        x = 42
    "#;

    let context = Context::logging(ccs_str, log::Level::Info)?;

    let augmented = context.constrain("a").constrain("c").constrain("d");
    assert_eq!(&augmented.get("x")?.to_type::<String>()?, "y");
    assert!(augmented.get("foobar").is_err());

    // Original context is untouched:
    assert_eq!(context.get("x")?.to_type::<i32>()?, 42);
    Ok::<(), ccs2::CcsError>(())
}
