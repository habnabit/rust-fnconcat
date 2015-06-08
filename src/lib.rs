#![feature(plugin_registrar, rustc_private, convert, slice_patterns)]

extern crate rustc;
extern crate syntax;

use std::rc::Rc;

use syntax::ast::{Delimited, TokenTree, TtDelimited, TtToken};
use syntax::codemap::Span;
use syntax::diagnostic::FatalError;
use syntax::ext::base::{DummyResult, ExtCtxt, MacEager, MacResult};
use syntax::ext::quote::rt::ToTokens;
use syntax::parse::token;
use syntax::util::small_vector::SmallVector;
use rustc::plugin::Registry;


macro_rules! fail {
    ($expr:expr) => (
        return Err(::std::convert::From::from($expr));
    )
}


#[derive(PartialEq, Eq, Clone, Debug)]
enum Error {
    OverSpan(Span, String),
    FatalParseError,
}

impl Error {
    fn as_mac_result(self, cx: &mut ExtCtxt, whole_span: Span) -> Box<MacResult + 'static> {
        let (span, message) = match self {
            Error::OverSpan(span, message) => (span, message),
            Error::FatalParseError => (whole_span, "fatal parse error".to_string()),
        };
        cx.span_err(span, message.as_str());
        DummyResult::any(span)
    }
}

impl From<(Span, &'static str)> for Error {
    fn from((err_span, err_string): (Span, &'static str)) -> Error {
        Error::OverSpan(err_span, err_string.to_string())
    }
}

impl From<FatalError> for Error {
    fn from(_: FatalError) -> Error {
        Error::FatalParseError
    }
}

type LocalResult<T> = Result<T, Error>;


fn tt_vec(tts: &[TokenTree]) -> Vec<TokenTree> {
    tts.iter().map(|tt| tt.clone()).collect()
}

fn ident_of_ctx_and_span(cx: &mut ExtCtxt, span: Span, ident: &str) -> TokenTree {
    TtToken(span, token::Ident(cx.ident_of(ident), token::Plain))
}

fn build_string_from_idents(target: &mut String, tts: &[TokenTree]) -> LocalResult<()> {
    for t in tts {
        match t {
            &TtToken(_, token::Ident(ref i, _)) => {
                target.extend(i.as_str().chars());
            },
            &TtToken(_, token::Comma) => (),
            &TtDelimited(delim_span, ref delim) => {
                if delim.delim != token::DelimToken::Bracket {
                    fail!((delim_span, "non-bracket delimiter"));
                }
                try!(build_string_from_idents(target, &delim.tts[..]));
            }
            ref tt => fail!((tt.get_span(), "non-ident, non-comma token")),
        }
    }
    Ok(())
}

fn fnconcat_impl(cx: &mut ExtCtxt, sp: Span, args: &[TokenTree]) -> LocalResult<Box<MacResult + 'static>> {
    if args.is_empty() {
        fail!((sp, "fnconcat! can't be called with nothing"));
    }
    let mut fn_tokens = tt_vec(args);
    fn_tokens[0] = if let &TtDelimited(delim_span, ref delim) = &fn_tokens[0] {
        if delim.delim != token::DelimToken::Bracket {
            fail!((delim_span, "use square brackets (i.e. [..]) in place of the function name"));
        }
        let mut concatenated = String::new();
        try!(build_string_from_idents(&mut concatenated, &delim.tts));
        if concatenated.is_empty() {
            fail!((delim_span, "empty identifier"));
        }
        ident_of_ctx_and_span(cx, delim_span, concatenated.as_str())
    } else {
        fail!((fn_tokens[0].get_span(), "use square brackets (i.e. [..]) in place of the function name"));
    };
    fn_tokens.insert(0, ident_of_ctx_and_span(cx, sp, "fn"));
    let mut p = cx.new_parser_from_tts(&fn_tokens[..]);
    if let Some(i) = p.parse_item() {
        return Ok(MacEager::items(SmallVector::one(i)));
    }
    fail!((sp, "couldn't parse a fn"));
}

fn fnconcat(cx: &mut ExtCtxt, sp: Span, args: &[TokenTree]) -> Box<MacResult + 'static> {
    match fnconcat_impl(cx, sp, args) {
        Ok(r) => r,
        Err(e) => e.as_mac_result(cx, sp),
    }
}


fn pull_tts_from_paren_groups(tts: &[TokenTree]) -> LocalResult<Vec<(Span, Vec<TokenTree>)>> {
    let mut ret = Vec::new();
    for t in tts {
        match t {
            &TtDelimited(delim_span, ref delim) if delim.delim == token::DelimToken::Paren => {
                ret.push((delim_span, tt_vec(&delim.tts[..])));
            },
            &TtToken(_, token::Comma) => (),
            ref tt => fail!((tt.get_span(), "parenthesized group expected")),
        }
    }
    Ok(ret)
}

fn parse_pats_and_types(cx: &mut ExtCtxt, span: Span, tts: Vec<TokenTree>) -> LocalResult<Vec<Vec<TokenTree>>> {
    let mut ret = Vec::new();
    let mut parser = cx.new_parser_from_tts(&tts[..]);
    loop {
        let pat = try!(parser.parse_pat_nopanic());
        try!(parser.expect(&token::Colon));
        let ty = try!(parser.parse_ty_nopanic());
        let mut pat = pat.to_tokens(cx);
        pat.push(TtToken(span, token::Colon));
        pat.extend(ty.to_tokens(cx).into_iter());
        ret.push(pat);
        if !try!(parser.eat(&token::Comma)) {
            break;
        }
    }
    Ok(ret)
}

fn parse_exprs(cx: &mut ExtCtxt, tts: Vec<TokenTree>) -> LocalResult<Vec<Vec<TokenTree>>> {
    let mut ret = Vec::new();
    let mut parser = cx.new_parser_from_tts(&tts[..]);
    loop {
        ret.push(try!(parser.parse_expr_nopanic()).to_tokens(cx));
        if !try!(parser.eat(&token::Comma)) {
            break;
        }
    }
    Ok(ret)
}

fn let_of_pat_and_expr(cx: &mut ExtCtxt, span: Span, pat: Vec<TokenTree>, expr: Vec<TokenTree>) -> Vec<TokenTree> {
    let mut ret = vec![ident_of_ctx_and_span(cx, span, "let")];
    ret.extend(pat.into_iter());
    ret.push(TtToken(span, token::Eq));
    ret.extend(expr.into_iter());
    ret.push(TtToken(span, token::Semi));
    ret
}

fn test_fn_of_ident_and_block(cx: &mut ExtCtxt, span: Span, ident: String, block: Vec<TokenTree>) -> Vec<TokenTree> {
    vec![
        TtToken(span, token::Pound),
        TtDelimited(span, Rc::new(Delimited {
            delim: token::Bracket,
            open_span: span,
            tts: vec![ident_of_ctx_and_span(cx, span, "test")],
            close_span: span,
        })),
        ident_of_ctx_and_span(cx, span, "fn"),
        ident_of_ctx_and_span(cx, span, ident.as_str()),
        TtDelimited(span, Rc::new(Delimited {
            delim: token::Paren,
            open_span: span,
            tts: Vec::new(),
            close_span: span,
        })),
        TtDelimited(span, Rc::new(Delimited {
            delim: token::Brace,
            open_span: span,
            tts: block,
            close_span: span,
        })),
    ]
}

fn do_parametrization(cx: &mut ExtCtxt, span: Span, base_name: String, params: &Delimited, block: Vec<TokenTree>)
                      -> LocalResult<Box<MacResult + 'static>> {
    let mut tokens = Vec::new();
    let mut groups = try!(pull_tts_from_paren_groups(&params.tts[..]));
    let param_types = try!(parse_pats_and_types(cx, span, groups.remove(0).1));
    let param_exprs_vec: Vec<(Span, Vec<Vec<TokenTree>>)> =
        try!(groups.into_iter().map(|(span, tts)| parse_exprs(cx, tts).map(|parsed| (span, parsed))).collect());
    let codemap = cx.codemap();
    for (e, (exprs_span, exprs)) in param_exprs_vec.into_iter().enumerate() {
        let mut fn_block = Vec::new();
        for (pat, expr) in param_types.iter().cloned().zip(exprs.into_iter()) {
            fn_block.extend(let_of_pat_and_expr(cx, span, pat, expr).into_iter());
        }
        let mut fn_name = format!("{}_{}", base_name, e);
        match codemap.span_to_lines(exprs_span).map(|lines| lines.lines.iter().map(|li| li.line_index).min()) {
            Ok(Some(line)) => fn_name.extend(format!("_line_{}", line).chars()),
            _ => (),
        }
        fn_block.extend(block.iter().cloned());
        tokens.extend(test_fn_of_ident_and_block(cx, span, fn_name, fn_block).into_iter());
    }
    let mut parser = cx.new_parser_from_tts(&tokens[..]);
    let mut items = Vec::new();
    loop {
        match parser.parse_item() {
            Some(i) => items.push(i),
            None => break,
        }
    }
    Ok(MacEager::items(SmallVector::many(items)))
}

fn parametrize_test_impl(cx: &mut ExtCtxt, sp: Span, args: &[TokenTree]) -> LocalResult<Box<MacResult + 'static>> {
    match args {
        [ref name,
         TtToken(_, token::Comma),
         TtDelimited(params_span, ref params),
         TtToken(_, token::Comma),
         TtDelimited(block_span, ref block)] => {
            if params.delim != token::DelimToken::Bracket {
                fail!((params_span, "need square brackets around parameters"));
            }
            if block.delim != token::DelimToken::Brace {
                fail!((block_span, "need curly braces around block"));
            }
            if params.tts.len() < 2 {
                fail!((params_span, "need at least param types and one param"));
            }
            let mut concatenated = String::new();
            try!(build_string_from_idents(&mut concatenated, &[name.clone()]));
            if concatenated.is_empty() {
                fail!((name.get_span(), "empty identifier"));
            }
            do_parametrization(cx, sp, concatenated, params, block.tts.clone())
        },
        _ => fail!((sp, "badly-structured parametrize_test!")),
    }
}

fn parametrize_test(cx: &mut ExtCtxt, sp: Span, args: &[TokenTree]) -> Box<MacResult + 'static> {
    match parametrize_test_impl(cx, sp, args) {
        Ok(r) => r,
        Err(e) => e.as_mac_result(cx, sp),
    }
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("fnconcat", fnconcat);
    reg.register_macro("parametrize_test", parametrize_test);
}
