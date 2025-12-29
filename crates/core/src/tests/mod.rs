use crate::file;
use crate::syntax::lex::lex;
use chumsky::Parser;

const TEXTS: &[&str] = &[
    include_str!("main.cront"),
    include_str!("struct.cront"),
    include_str!("init.cront"),
];

#[test]
fn it_parses() {
    for text in TEXTS {
        let tokens = lex().parse(text).unwrap();
        file().parse(tokens.tokens.as_slice()).unwrap();
    }
}
