use cc::Build;
use std::path::Path;

pub fn build(file: &Path) {
    let target = env!("CC_TARGET");
    let compiler = Build::new()
        .cargo_metadata(false)
        .cargo_output(false)
        .host(target)
        .target(target)
        .debug(true)
        .opt_level(3)
        .std("c89")
        .get_compiler();
    let is_gnu_or_clang = compiler.is_like_gnu() || compiler.is_like_clang();
    let mut cmd = compiler.to_command();
    if is_gnu_or_clang {
        let out = file.with_extension(if cfg!(target_os = "windows") {
            "exe"
        } else if cfg!(debug_assertions) {
            "out"
        } else {
            ""
        });
        cmd.arg("-o").arg(out);
    };
    if !cmd.arg(file).spawn().unwrap().wait().unwrap().success() {
        panic!("build failed")
    }
}
