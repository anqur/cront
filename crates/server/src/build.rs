use cront_core::{build as compile, check, generate, parse, resolve};
use std::fmt::Write;
use std::fs::{read_to_string, write};
use std::path::Path;

pub(crate) fn build(path: &Path) {
    let out = path.with_extension("c");
    let text = read_to_string(path).unwrap();
    let mut file = parse(&text);
    resolve(&mut file).unwrap();
    let mut code = generate(check(&mut file).unwrap());
    // FIXME: Entry function.
    writeln!(code).unwrap();
    writeln!(code, "int main() {{ return 0; }}").unwrap();
    write(&out, code).unwrap();
    compile(&out);
}
