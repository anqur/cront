use crate::syntax::parse::parse;
use crate::{build, check, generate, resolve};
use std::fs::{read_to_string, write};
use std::path::PathBuf;
use std::process::Command;

fn test_dir() -> PathBuf {
    PathBuf::new()
        .join(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("tests")
}

const PARSE_TEXTS: &[&str] = &[
    include_str!("println.cront"),
    include_str!("vector.cront"),
    include_str!("struct.cront"),
];

#[test]
fn it_parses() {
    for text in PARSE_TEXTS {
        parse(text);
    }
}

const RESOLVE_TEXTS: &[&str] = &[
    include_str!("factorial.cront"),
    include_str!("struct.cront"),
];

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
    include_str!("struct.cront"),
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
    include_str!("struct.cront"),
];

#[test]
fn it_generates() {
    for text in GENERATION_TEXTS {
        let mut file = parse(text);
        resolve(&mut file).unwrap();
        print!("{}", generate(check(&mut file).unwrap()));
    }
}

const BUILD_FILES: &[&str] = &["factorial.cront", "generic.cront", "struct.cront"];

#[test]
fn it_builds() {
    for file in BUILD_FILES {
        let path = test_dir().join(file);
        let out = path.with_extension("c");
        let text = read_to_string(&path).unwrap();
        let mut file = parse(&text);
        resolve(&mut file).unwrap();
        write(&out, generate(check(&mut file).unwrap())).unwrap();
        build(&out);
    }
}

#[test]
#[ignore]
fn it_runs() {
    let mut found = false;
    test_dir()
        .read_dir()
        .unwrap()
        .filter_map(Result::ok)
        .filter(|e| e.file_type().unwrap().is_file())
        .filter_map(|f| {
            let path = f.path();
            if matches!( path.extension(), Some(ext) if ext == "exe" || ext == "out") {
                return Some(path);
            }
            None
        })
        .for_each(|f| {
            found = true;
            assert!(Command::new(f).spawn().unwrap().wait().unwrap().success())
        });
    assert!(found);
}
