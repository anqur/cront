use crate::syntax::lex::lex;
use crate::{file, resolve};
use chumsky::Parser;

const PARSING_TEXTS: &[&str] = &[include_str!("main.cront"), include_str!("struct.cront")];

#[test]
fn it_parses() {
    for text in PARSING_TEXTS {
        let tokens = lex().parse(text).unwrap();
        file().parse(tokens.tokens.as_slice()).unwrap();
    }
}

const RESOLVING_TEXTS: &[&str] = &[include_str!("factorial.cront")];

#[test]
fn it_resolves() {
    for text in RESOLVING_TEXTS {
        let tokens = lex().parse(text).unwrap();
        let mut file = file().parse(tokens.tokens.as_slice()).unwrap();
        resolve(&mut file).unwrap();
    }
}
