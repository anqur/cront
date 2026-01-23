use crate::syntax::parse::parse;
use crate::{build, check, generate, resolve};
use std::fs::{read_to_string, write};
use std::path::PathBuf;

const PARSE_TEXTS: &[&str] = &[include_str!("main.cront"), include_str!("struct.cront")];

#[test]
fn it_parses() {
    for text in PARSE_TEXTS {
        parse(text);
    }
}

const RESOLVE_TEXTS: &[&str] = &[include_str!("factorial.cront")];

#[test]
fn it_resolves() {
    for text in RESOLVE_TEXTS {
        let mut file = parse(text);
        resolve(&mut file).unwrap();
    }
}

const CHECK_TEXTS: &[&str] = &[
    include_str!("factorial.cront"),
    include_str!("generic.cront"),
];

#[test]
fn it_checks() {
    for text in CHECK_TEXTS {
        let mut file = parse(text);
        resolve(&mut file).unwrap();
        check(&mut file).unwrap();
    }
}

const GENERATION_TEXTS: &[&str] = &[
    include_str!("factorial.cront"),
    include_str!("generic.cront"),
];

#[test]
fn it_generates() {
    for text in GENERATION_TEXTS {
        let mut file = parse(text);
        resolve(&mut file).unwrap();
        print!("{}", generate(check(&mut file).unwrap()));
    }
}

const BUILD_FILES: &[&str] = &[
    "factorial.cront",
    // TODO: Monomorphization.
    //"generic.cront",
];

#[test]
fn it_builds() {
    for file in BUILD_FILES {
        let path = PathBuf::new()
            .join(env!("CARGO_MANIFEST_DIR"))
            .join("src")
            .join("tests")
            .join(file);
        let out = path.with_extension("c");
        let text = read_to_string(&path).unwrap();
        let mut file = parse(&text);
        resolve(&mut file).unwrap();
        write(&out, generate(check(&mut file).unwrap())).unwrap();
        build(&out);
    }
}
