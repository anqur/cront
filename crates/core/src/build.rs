use cc::Build;
use std::path::Path;

pub fn build(file: &Path) {
    let target = env!("CC_TARGET");
    let mut builder = Build::new();
    builder
        .cargo_metadata(false)
        .cargo_output(false)
        .host(target)
        .target(target)
        .debug(true)
        .opt_level(3)
        .std("c89");
    #[cfg(debug_assertions)]
    {
        builder.warnings_into_errors(true);
    }
    let compiler = builder.get_compiler();
    let is_gnu_or_clang = compiler.is_like_gnu() || compiler.is_like_clang();
    let is_msvc = compiler.is_like_msvc();
    let mut cmd = compiler.to_command();
    let out = file.with_extension(if cfg!(target_os = "windows") {
        "exe"
    } else if cfg!(debug_assertions) {
        "out"
    } else {
        ""
    });
    if is_gnu_or_clang {
        cmd.arg("-o").arg(out);
    } else if is_msvc {
        cmd.arg(format!("/Fe:{}", out.display()));
    }
    if !cmd.arg(file).spawn().unwrap().wait().unwrap().success() {
        panic!("build failed")
    }
}
