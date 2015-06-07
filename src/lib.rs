#![feature(plugin_registrar, rustc_private, convert, slice_patterns)]

extern crate rustc;
extern crate syntax;

use std::rc::Rc;

use syntax::codemap::Span;
use syntax::parse::{PResult, token};
use syntax::ast::{Delimited, Ident, TokenTree, TtDelimited, TtToken};
use syntax::ext::base::{ExtCtxt, MacResult, DummyResult, MacEager};
use syntax::ext::quote::rt::ToTokens;
use syntax::util::small_vector::SmallVector;
use rustc::plugin::Registry;


fn tt_vec(tts: &[TokenTree]) -> Vec<TokenTree> {
    tts.iter().map(|tt| tt.clone()).collect()
}

fn ident_of_ctx_and_span(cx: &mut ExtCtxt, span: Span, ident: &str) -> TokenTree {
    TtToken(span, token::Ident(cx.ident_of(ident), token::Plain))
}

fn build_string_from_idents(target: &mut String, tts: &[TokenTree]) -> Result<(), Span> {
    for t in tts {
        match t {
            &TtToken(_, token::Ident(ref i, _)) => {
                target.extend(i.as_str().chars());
            },
            &TtToken(_, token::Comma) => (),
            &TtDelimited(delim_span, ref delim) => {
                if delim.delim != token::DelimToken::Bracket {
                    return Err(delim_span);
                }
                try!(build_string_from_idents(target, &delim.tts[..]));
            }
            ref tt => return Err(tt.get_span()),
        }
    }
    Ok(())
}

fn fnconcat(cx: &mut ExtCtxt, sp: Span, args: &[TokenTree])
            -> Box<MacResult + 'static> {
    if args.is_empty() {
        cx.span_err(sp, "fnconcat! can't be called with nothing");
        return DummyResult::any(sp);
    }
    let mut fn_tokens = tt_vec(args);
    fn_tokens[0] = if let &TtDelimited(delim_span, ref delim) = &fn_tokens[0] {
        if delim.delim != token::DelimToken::Bracket {
            cx.span_err(delim_span, "use square brackets (i.e. [..]) in place of the function name");
            return DummyResult::any(delim_span);
        }
        let mut concatenated = String::new();
        match build_string_from_idents(&mut concatenated, &delim.tts) {
            Ok(()) => (),
            Err(err_span) => {
                cx.span_err(err_span, "non-ident, non-comma token");
                return DummyResult::any(sp);
            },
        }
        if concatenated.is_empty() {
            cx.span_err(delim_span, "empty identifier");
            return DummyResult::any(sp);
        }
        ident_of_ctx_and_span(cx, delim_span, concatenated.as_str())
    } else {
        cx.span_err(sp, "use square brackets (i.e. [..]) in place of the function name");
        return DummyResult::any(sp);
    };
    fn_tokens.insert(0, ident_of_ctx_and_span(cx, sp, "fn"));
    let mut p = cx.new_parser_from_tts(&fn_tokens[..]);
    if let Some(i) = p.parse_item() {
        return MacEager::items(SmallVector::one(i));
    }
    cx.span_err(sp, "couldn't parse a fn");
    return DummyResult::any(sp);
}


fn pull_tts_from_paren_groups(tts: &[TokenTree]) -> PResult<Vec<Vec<TokenTree>>> {
    let mut ret = Vec::new();
    for t in tts {
        match t {
            &TtDelimited(_, ref delim) if delim.delim == token::DelimToken::Paren => {
                ret.push(tt_vec(&delim.tts[..]));
            },
            _ => {

            },
        }
    }
    Ok(ret)
}

fn parse_pats_and_types(cx: &mut ExtCtxt, span: Span, tts: Vec<TokenTree>) -> PResult<Vec<Vec<TokenTree>>> {
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

fn parse_exprs(cx: &mut ExtCtxt, tts: Vec<TokenTree>) -> PResult<Vec<Vec<TokenTree>>> {
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

fn do_parametrization(cx: &mut ExtCtxt, span: Span, base_name: Ident, params: &Delimited, block: Vec<TokenTree>)
                      -> PResult<Box<MacResult + 'static>> {
    let mut tokens = Vec::new();
    let mut groups = try!(pull_tts_from_paren_groups(&params.tts[..]));
    let param_types = try!(parse_pats_and_types(cx, span, groups.remove(0)));
    let param_exprs_vec: Vec<Vec<Vec<TokenTree>>> = try!(groups.into_iter().map(|tts| parse_exprs(cx, tts)).collect());
    for (e, exprs) in param_exprs_vec.into_iter().enumerate() {
        let mut fn_block = Vec::new();
        for (pat, expr) in param_types.iter().cloned().zip(exprs.into_iter()) {
            fn_block.extend(let_of_pat_and_expr(cx, span, pat, expr).into_iter());
        }
        fn_block.extend(block.iter().cloned());
        let fn_name = format!("{}_{}", base_name.as_str(), e);
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

fn parametrize_test(cx: &mut ExtCtxt, sp: Span, args: &[TokenTree])
                    -> Box<MacResult + 'static> {
    match args {
        [TtToken(_, token::Ident(ref name, _)),
         TtToken(_, token::Comma),
         TtDelimited(params_span, ref params),
         TtToken(_, token::Comma),
         TtDelimited(block_span, ref block)] => {
            if params.delim != token::DelimToken::Bracket {
                cx.span_err(params_span, "need square brackets around parameters");
                return DummyResult::any(params_span);
            }
            if block.delim != token::DelimToken::Brace {
                cx.span_err(block_span, "need curly braces around block");
                return DummyResult::any(block_span);
            }
            if params.tts.len() < 2 {
                cx.span_err(params_span, "need at least param types and one param");
                return DummyResult::any(params_span);
            }
            match do_parametrization(cx, sp, name.clone(), params, block.tts.clone()) {
                Ok(r) => return r,
                Err(_) => {
                    cx.span_err(sp, "error while parsing");
                    return DummyResult::any(sp);
                }
            }
        },
        _ => {
            cx.span_err(sp, "badly-structured parametrize_test!");
            return DummyResult::any(sp);
        }
    }
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("fnconcat", fnconcat);
    reg.register_macro("parametrize_test", parametrize_test);
}
