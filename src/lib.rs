#![feature(plugin_registrar, rustc_private, convert, slice_patterns)]

extern crate rustc;
extern crate syntax;

use syntax::codemap::{Spanned, Span};
use syntax::parse::{PResult, token};
use syntax::ast::{TokenTree, TtDelimited, TtToken};
use syntax::{abi, ast};
use syntax::ext::base::{ExtCtxt, MacResult, DummyResult, MacEager};
use syntax::ptr::P;
use syntax::owned_slice::OwnedSlice;
use syntax::util::small_vector::SmallVector;
use rustc::plugin::Registry;


fn tt_vec(tts: &[TokenTree]) -> Vec<TokenTree> {
    tts.iter().map(|tt| tt.clone()).collect()
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

fn parse_pats_and_types(cx: &mut ExtCtxt, tts: Vec<TokenTree>) -> PResult<Vec<(P<ast::Pat>, P<ast::Ty>)>> {
    let mut ret = Vec::new();
    let mut parser = cx.new_parser_from_tts(&tts[..]);
    loop {
        let pat = try!(parser.parse_pat_nopanic());
        try!(parser.expect(&token::Colon));
        let ty = try!(parser.parse_ty_nopanic());
        ret.push((pat, ty));
        if !try!(parser.eat(&token::Comma)) {
            break;
        }
    }
    Ok(ret)
}

fn parse_exprs(cx: &mut ExtCtxt, tts: Vec<TokenTree>) -> PResult<Vec<P<ast::Expr>>> {
    let mut ret = Vec::new();
    let mut parser = cx.new_parser_from_tts(&tts[..]);
    loop {
        ret.push(try!(parser.parse_expr_nopanic()));
        if !try!(parser.eat(&token::Comma)) {
            break;
        }
    }
    Ok(ret)
}

fn let_of_pat_type_and_expr(pat: P<ast::Pat>, ty: P<ast::Ty>, expr: P<ast::Expr>, span: Span) -> P<ast::Stmt> {
    let id = pat.id;
    let local = ast::Local {
        pat: pat,
        ty: Some(ty),
        init: Some(expr),
        id: id,
        span: span.clone(),
        source: ast::LocalLet,
    };
    let decl = ast::DeclLocal(P(local));
    let stmt = ast::StmtDecl(P(Spanned { node: decl, span: span.clone() }), id);
    P(Spanned { node: stmt, span: span })
}

fn unit_output(id: ast::NodeId, sp: Span) -> ast::FunctionRetTy {
    let ty = ast::Ty {
        id: id,
        node: ast::TyTup(Vec::new()),
        span: sp.clone(),
    };
    ast::Return(P(ty))
}

fn test_fn_item_of_ident_and_block(sp: Span, ident: ast::Ident, block: P<ast::Block>) -> P<ast::Item> {
    let id = block.id;
    let fn_decl = P(ast::FnDecl {
        inputs: Vec::new(),
        output: unit_output(id, sp),
        variadic: false,
    });
    let generics = ast::Generics {
        lifetimes: Vec::new(),
        ty_params: OwnedSlice::empty(),
        where_clause: ast::WhereClause {
            id: id,
            predicates: Vec::new(),
        },
    };
    let item_fn = ast::ItemFn(
        fn_decl,
        ast::Unsafety::Normal,
        ast::Constness::NotConst,
        abi::Rust,
        generics,
        block,
        );
    let test_attribute = ast::Attribute_ {
        id: ast::AttrId(0),
        style: ast::AttrOuter,
        value: P(Spanned { node: ast::MetaWord(token::InternedString::new("test")), span: sp.clone() }),
        is_sugared_doc: false,
    };
    P(ast::Item {
        ident: ident,
        attrs: vec![Spanned { node: test_attribute, span: sp.clone() }],
        id: id,
        node: item_fn,
        vis: ast::Public,
        span: sp,
    })
}

fn do_parametrization(cx: &mut ExtCtxt, sp: Span, base_name: ast::Ident,
                      params: &ast::Delimited, whole_block: TokenTree)
                      -> PResult<Box<MacResult + 'static>> {
    let mut items = Vec::new();
    let mut groups = try!(pull_tts_from_paren_groups(&params.tts[..]));
    let param_types = try!(parse_pats_and_types(cx, groups.remove(0)));
    let param_exprs_vec: Vec<Vec<P<ast::Expr>>> = try!(groups.into_iter().map(|tts| parse_exprs(cx, tts)).collect());
    let block = try!(cx.new_parser_from_tts(&vec![whole_block][..]).parse_block());
    for (e, exprs) in param_exprs_vec.into_iter().enumerate() {
        let mut new_stmts = Vec::new();
        for ((pat, ty), expr) in param_types.iter().cloned().zip(exprs.into_iter()) {
            new_stmts.push(let_of_pat_type_and_expr(pat, ty, expr, sp))
        }
        new_stmts.extend(block.stmts.iter().cloned());
        let param_block = P(ast::Block {
            stmts: new_stmts,
            .. (*block).clone()
        });
        let fn_name = format!("{}_{}", base_name.as_str(), e);
        let ident = cx.ident_of(fn_name.as_str());
        items.push(test_fn_item_of_ident_and_block(sp.clone(), ident, param_block));
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
            match do_parametrization(cx, sp, name.clone(), params, TtDelimited(block_span, block.clone())) {
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
