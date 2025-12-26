use crate::file;
use crate::syntax::lex::lex;
use chumsky::Parser;

#[test]
fn it_parses() {
    let tokens = lex().parse(include_str!("hello.cront")).unwrap();
    file().parse(tokens.tokens.as_slice()).unwrap();
}
