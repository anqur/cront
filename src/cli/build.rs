use crate::backend::codegen::generate;
use crate::backend::compile::compile;
use crate::frontend::parse::parse;
use crate::middleend::check::check;
use crate::middleend::resolve::resolve;
use std::fs::{read_to_string, write};
use std::path::Path;

pub fn build(path: &Path) {
    let out = path.with_extension("c");
    let text = read_to_string(path).unwrap();
    let mut file = parse(&text);
    resolve(&mut file).unwrap();
    write(&out, generate(check(&mut file).unwrap())).unwrap();
    compile(&out);
}
