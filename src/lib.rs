#![feature(plugin_registrar, rustc_private, convert)]

extern crate rustc;
extern crate syntax;

use syntax::codemap::Span;
use syntax::parse::token;
use syntax::ast::{TokenTree, TtDelimited, TtToken};
use syntax::ext::base::{ExtCtxt, MacResult, DummyResult, MacEager};
use syntax::util::small_vector::SmallVector;
use rustc::plugin::Registry;


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
    let mut fn_tokens: Vec<TokenTree> = args.iter().map(|tt| tt.clone()).collect();
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
        TtToken(sp, token::Ident(cx.ident_of(concatenated.as_str()), token::Plain))
    } else {
        cx.span_err(sp, "use square brackets (i.e. [..]) in place of the function name");
        return DummyResult::any(sp);
    };
    fn_tokens.insert(0, TtToken(sp, token::Ident(cx.ident_of("fn"), token::Plain)));
    let mut p = cx.new_parser_from_tts(&fn_tokens[..]);
    if let Some(i) = p.parse_item() {
        return MacEager::items(SmallVector::one(i));
    }
    cx.span_err(sp, "couldn't parse a fn");
    return DummyResult::any(sp);
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("fnconcat", fnconcat);
}
