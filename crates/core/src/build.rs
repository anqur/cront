use cc::Build;
use std::path::Path;

// FIXME: Should not be public.
pub fn build(file: &Path) {
    let target = env!("CC_TARGET");
    Build::new()
        .cargo_metadata(false)
        .cargo_output(false)
        .host(target)
        .target(target)
        .debug(true)
        .opt_level(3)
        .std("c11")
        .get_compiler()
        .to_command()
        .arg(file)
        .spawn()
        .unwrap()
        .wait()
        .unwrap();
}
