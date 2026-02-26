mod lex;
mod parse;

use crate::Span;
use chumsky::container::{OrderedSeq, Seq};
use chumsky::input::{Cursor, ValueInput};
use chumsky::inspector::Inspector;
use chumsky::prelude::Input;
use chumsky::span::SimpleSpan;
use chumsky::util::{Maybe, MaybeRef};
use cstree::Syntax;
use cstree::build::{Checkpoint, NodeCache};
use cstree::prelude::{GreenNodeBuilder, SyntaxNode};
use std::ops::Range;

struct Tokens<'t>(&'t [Span<Kind>]);

impl<'t> From<&'t [Span<Kind>]> for Tokens<'t> {
    fn from(t: &'t [Span<Kind>]) -> Self {
        Self(t)
    }
}

impl<'t> Input<'t> for Tokens<'t> {
    type Span = SimpleSpan;
    type Token = Span<Kind>;
    type MaybeToken = Span<Kind>;
    type Cursor = usize;
    type Cache = Self;

    fn begin(self) -> (Self::Cursor, Self::Cache) {
        (0, self)
    }

    fn cursor_location(cursor: &Self::Cursor) -> usize {
        *cursor
    }

    unsafe fn next_maybe(
        cache: &mut Self::Cache,
        cursor: &mut Self::Cursor,
    ) -> Option<Self::MaybeToken> {
        if *cursor >= cache.0.len() {
            None
        } else {
            let token = cache.0[*cursor].clone();
            *cursor += 1;
            Some(token)
        }
    }

    unsafe fn span(cache: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Span {
        let start = if cache.0.is_empty() {
            0
        } else if *range.start >= cache.0.len() {
            cache.0[*range.start - 1].span.end
        } else {
            cache.0[*range.start].span.start
        };
        let end = if cache.0.is_empty() {
            0
        } else if *range.end == cache.0.len() {
            cache.0.last().unwrap().span.end
        } else {
            cache.0[*range.end].span.start
        };
        SimpleSpan::from(start..end)
    }
}

impl<'t> ValueInput<'t> for Tokens<'t> {
    unsafe fn next(cache: &mut Self::Cache, cursor: &mut Self::Cursor) -> Option<Self::Token> {
        unsafe { Tokens::next_maybe(cache, cursor) }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Syntax)]
#[repr(u32)]
enum Kind {
    // Declaration nodes.
    File,
    Fun,
    Typ,
    Struct,

    // Parametrized nodes.
    Param,
    Constr,

    // Statement nodes.
    StmtAssign,
    StmtUpdate,
    StmtBreak,
    StmtContinue,
    StmtReturn,
    StmtExpr,
    StmtIf,
    StmtWhile,

    // Branch nodes.
    Branch,
    BranchCond,
    BranchElse,

    // Expression nodes.
    ExprArrayType,
    ExprRefType,
    ExprBinaryOp,
    ExprCall,

    // Call expression nodes.
    CallArgs,
    CallObject,
    CallMethod,
    CallAccess,
    CallTypeArgs,

    // Blanks.
    Whitespace,
    Newline,

    // Comments.
    Doc,
    LineComment,
    BlockComment,

    // Keywords.
    KwTrue,
    KwFalse,
    KwFun,
    KwLet,
    KwIf,
    KwElse,
    KwFor,
    KwWhile,
    KwBreak,
    KwContinue,
    KwReturn,
    KwStruct,
    KwTyp,

    // Type keywords.
    KwVoid,
    KwBool,
    KwI8,
    KwI16,
    KwI32,
    KwI64,
    KwU8,
    KwU16,
    KwU32,
    KwU64,
    KwUSize,
    KwF32,
    KwF64,
    KwStr,
    KwNumber,
    KwType,

    // Long symbols.
    SymEqEq,
    SymLe,
    SymGe,
    SymColonColon,

    // One-character symbols.
    SymLParen,
    SymRParen,
    SymLBrace,
    SymRBrace,
    SymLBracket,
    SymRBracket,
    SymLt,
    SymGt,
    SymSemi,
    SymColon,
    SymComma,
    SymDot,
    SymEq,
    SymPlus,
    SymMinus,
    SymMul,
    SymAnd,
    SymQuestion,

    // Specials.
    Number,
    String,
    Ident,
    Error,
}

impl<'t> Seq<'t, Span<Kind>> for Kind {
    type Item<'a> = Span<Kind>;
    type Iter<'a> = std::iter::Once<Span<Kind>>;

    fn seq_iter(&self) -> Self::Iter<'_> {
        std::iter::once(Span {
            span: SimpleSpan::from(0..0),
            item: *self,
        })
    }

    fn contains(&self, val: &Span<Kind>) -> bool {
        val.item == *self
    }

    fn to_maybe_ref<'b>(item: Self::Item<'b>) -> MaybeRef<'t, Span<Kind>>
    where
        't: 'b,
    {
        Maybe::Val(item)
    }
}

impl<'t> OrderedSeq<'t, Span<Kind>> for Kind {}

struct Builder<'src> {
    src: &'src str,
    builder: GreenNodeBuilder<'static, 'static, Kind>,
}

impl<'t> Builder<'t> {
    fn new(src: &'t str) -> Self {
        Self {
            src,
            builder: GreenNodeBuilder::new(),
        }
    }

    pub(super) fn checkpoint(&self) -> Checkpoint {
        self.builder.checkpoint()
    }

    pub(super) fn insert(&mut self, c: Checkpoint, kind: Kind) {
        self.builder.start_node_at(c, kind);
        self.builder.finish_node();
    }

    pub(super) fn finish(self) -> (SyntaxNode<Kind>, NodeCache<'static>) {
        let (node, cache) = self.builder.finish();
        (SyntaxNode::new_root(node), cache.unwrap())
    }
}

impl<'t> Inspector<'t, Tokens<'t>> for Builder<'t> {
    type Checkpoint = Checkpoint;

    fn on_token(&mut self, token: &Span<Kind>) {
        let slice = &self.src[token.span.into_range()];
        self.builder.token(token.item, slice);
    }

    fn on_save<'parse>(&self, _: &Cursor<'t, 'parse, Tokens<'t>>) -> Self::Checkpoint {
        self.builder.checkpoint()
    }

    fn on_rewind<'parse>(
        &mut self,
        marker: &chumsky::input::Checkpoint<'t, 'parse, Tokens<'t>, Self::Checkpoint>,
    ) {
        self.builder.revert_to(*marker.inspector())
    }
}

#[cfg(test)]
mod test {
    use crate::frontend::cst::{lex, parse};

    #[test]
    fn it_parses_expr() {
        const TEXT: &str = "1 + 2";
        let lexed = lex::State::lex(TEXT);
        assert!(lexed.errs.is_empty());
        let parsed = parse::State::parse_expr(&lexed.src, &lexed.tokens);
        assert!(parsed.errs.is_empty());
        // TODO: Snapshots.
        println!("{}", parsed.cst.debug(parsed.cache.interner(), true));
    }

    #[test]
    fn it_parses_stmt() {
        const TEXT: &str = r#"if f(a) {
    let a: U32 = 1;
    return a + 2;
} else if b + c {
    return 42;
}"#;
        let lexed = lex::State::lex(TEXT);
        assert!(lexed.errs.is_empty());
        let parsed = parse::State::parse_stmt(&lexed.src, &lexed.tokens);
        assert!(parsed.errs.is_empty());
        // TODO: Snapshots.
        println!("{}", parsed.cst.debug(parsed.cache.interner(), true));
    }

    #[test]
    fn it_parses_factorial() {
        const TEXT: &str = r#"
fun factorial(n: U32) U32 {
    let a: U32 = 1;
    while n > 1 {
        a = a * n;
        n = n - 1;
    }
    return a;
}
"#;
        let lexed = lex::State::lex(TEXT);
        assert!(lexed.errs.is_empty());
        let parsed = parse::State::parse(&lexed.src, &lexed.tokens);
        assert!(parsed.errs.is_empty());
        // TODO: Snapshots.
        println!("{}", parsed.cst.debug(parsed.cache.interner(), true));
    }
}
