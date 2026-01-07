use crate::syntax::lex::lex;
use crate::syntax::parse::File;
use crate::{check, file, resolve};
use chumsky::Parser;

fn parse(text: &str) -> File {
    let tokens = lex().parse(text).unwrap();
    file().parse(tokens.tokens.as_slice()).unwrap()
}

const PARSING_TEXTS: &[&str] = &[include_str!("main.cront"), include_str!("struct.cront")];

#[test]
fn it_parses() {
    for text in PARSING_TEXTS {
        parse(text);
    }
}

const RESOLVING_TEXTS: &[&str] = &[include_str!("factorial.cront")];

#[test]
fn it_resolves() {
    for text in RESOLVING_TEXTS {
        let mut file = parse(text);
        resolve(&mut file).unwrap();
    }
}

const CHECKING_TEXTS: &[&str] = &[include_str!("factorial.cront")];

#[test]
fn it_checks() {
    for text in CHECKING_TEXTS {
        let mut file = parse(text);
        resolve(&mut file).unwrap();
        check(&mut file).unwrap();
    }
}
