use crate::parse::lex::lex;
use chumsky::Parser;

#[test]
fn it_scans() {
    lex().parse(include_str!("hello.cront")).unwrap();
}
