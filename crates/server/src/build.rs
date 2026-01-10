use cront_core::{build as compile, check, generate, parse, resolve};
use std::fs::{read_to_string, write};
use std::path::Path;

pub(crate) fn build(path: &Path) {
    let out = path.with_extension("c");
    let text = read_to_string(path).unwrap();
    let mut file = parse(&text);
    resolve(&mut file).unwrap();
    write(&out, generate(check(&mut file).unwrap())).unwrap();
    compile(&out);
}
