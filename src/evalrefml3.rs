mod rule;

use std::{
    collections::HashMap,
    hash::Hash,
    io,
    ops::{Deref, DerefMut},
};

use crate::common;

use self::rule::{
    Env, EnvList, Exp, Fxp, Gxp, Hxp, Ixp, Judgement, Jxp, Kxp, LocList, LongExp, Parser,
    PostStore, PreStore, Value, ARROW, COMMA, EQ, EVALTO, FUN, IS, LBRACKET, LESS, LOC, LPAREN,
    MINUS, NUM, PLUS, RBRACKET, REC, RPAREN, SLASH, THAN, TIMES, TRUTH, VAR, VDASH,
};

#[derive(Debug)]
struct Derivation(Judgement, Box<Rule>);
impl std::fmt::Display for Derivation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} by {}", self.0, self.1)
    }
}

#[derive(Debug)]
enum Rule {
    EInt,
    EBool,
    EVar,
    EIfT(Derivation, Derivation),
    EIfF(Derivation, Derivation),
    EPlus(Derivation, Derivation, Derivation),
    EMinus(Derivation, Derivation, Derivation),
    ETimes(Derivation, Derivation, Derivation),
    ELt(Derivation, Derivation, Derivation),
    ELet(Derivation, Derivation),
    EFun,
    EApp(Derivation, Derivation, Derivation),
    ELetRec(Derivation),
    EAppRec(Derivation, Derivation, Derivation),
    ERef(Derivation),
    EDeref(Derivation),
    EAssign(Derivation, Derivation),
    BPlus,
    BMinus,
    BTimes,
    BLt,
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::EInt => write!(f, "E-Int {{}}"),
            Rule::EBool => write!(f, "E-Bool {{}}"),
            Rule::EVar => write!(f, "E-Var {{}}"),
            Rule::EIfT(d0, d1) => write!(f, "E-IfT {{{};{}}}", d0, d1),
            Rule::EIfF(d0, d1) => write!(f, "E-IfF {{{};{}}}", d0, d1),
            Rule::EPlus(d0, d1, d2) => write!(f, "E-Plus {{{};{};{}}}", d0, d1, d2),
            Rule::EMinus(d0, d1, d2) => write!(f, "E-Minus {{{};{};{}}}", d0, d1, d2),
            Rule::ETimes(d0, d1, d2) => write!(f, "E-Times {{{};{};{}}}", d0, d1, d2),
            Rule::ELt(d0, d1, d2) => write!(f, "E-Lt {{{};{};{}}}", d0, d1, d2),
            Rule::ELet(d0, d1) => write!(f, "E-Let {{{};{}}}", d0, d1),
            Rule::EFun => write!(f, "E-Fun {{}}"),
            Rule::EApp(d0, d1, d2) => write!(f, "E-App {{{};{};{}}}", d0, d1, d2),
            Rule::ELetRec(d0) => write!(f, "E-LetRec {{{}}}", d0),
            Rule::EAppRec(d0, d1, d2) => write!(f, "E-AppRec {{{};{};{}}}", d0, d1, d2),
            Rule::ERef(d0) => write!(f, "E-Ref {{{}}}", d0),
            Rule::EDeref(d0) => write!(f, "E-Deref {{{}}}", d0),
            Rule::EAssign(d0, d1) => write!(f, "E-Assign {{{};{}}}", d0, d1),
            Rule::BPlus => write!(f, "B-Plus {{}}"),
            Rule::BMinus => write!(f, "B-Minus {{}}"),
            Rule::BTimes => write!(f, "B-Times {{}}"),
            Rule::BLt => write!(f, "B-Lt {{}}"),
        }
    }
}

impl Hash for LOC {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

fn hoge(posts0: &PostStore, posts1: &PostStore) -> io::Result<HashMap<LOC, LOC>> {
    match (posts0, posts1) {
        (PostStore::PostStore0(_, ll0), PostStore::PostStore0(_, ll1)) => {
            match (ll0.deref(), ll1.deref()) {
                (LocList::LocList0(ll0_, _, l0, _, _), LocList::LocList0(ll1_, _, l1, _, _)) => {
                    let mut map = hoge(
                        &PostStore::PostStore0(Box::new(SLASH::new("/")), ll0_.clone()),
                        &PostStore::PostStore0(Box::new(SLASH::new("/")), ll1_.clone()),
                    )?;
                    map.insert(l0.deref().clone(), l1.deref().clone());
                    Ok(map)
                }

                (LocList::LocList1(l0, _, _), LocList::LocList1(l1, _, _)) => {
                    let mut map = HashMap::new();
                    map.insert(l0.deref().clone(), l1.deref().clone());
                    Ok(map)
                }

                _ => Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                )),
            }
        }

        (PostStore::PostStore1(), PostStore::PostStore1()) => Ok(HashMap::new()),

        _ => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        )),
    }
}

fn rename(d: &mut Derivation, map: &HashMap<LOC, LOC>) {
    let Derivation(j, rule) = d;

    if let Judgement::Judgement0(pres, env, _, _, _, v, posts) = j {
        rename_pres(pres, map);
        rename_env(env, map);
        rename_value(v, map);
        rename_posts(posts, map);
    }

    match rule.deref_mut() {
        Rule::EInt
        | Rule::EBool
        | Rule::EVar
        | Rule::BPlus
        | Rule::BMinus
        | Rule::BTimes
        | Rule::BLt
        | Rule::EFun => {}

        Rule::ELetRec(d0) | Rule::ERef(d0) | Rule::EDeref(d0) => {
            rename(d0, map);
        }

        Rule::EIfT(d0, d1) | Rule::EIfF(d0, d1) | Rule::ELet(d0, d1) | Rule::EAssign(d0, d1) => {
            rename(d0, map);
            rename(d1, map);
        }

        Rule::EPlus(d0, d1, d2)
        | Rule::EMinus(d0, d1, d2)
        | Rule::ETimes(d0, d1, d2)
        | Rule::ELt(d0, d1, d2)
        | Rule::EApp(d0, d1, d2)
        | Rule::EAppRec(d0, d1, d2) => {
            rename(d0, map);
            rename(d1, map);
            rename(d2, map);
        }
    }
}

fn rename_value(v: &mut Value, map: &HashMap<LOC, LOC>) {
    match v {
        Value::Value0(_) | Value::Value1(_) => {}
        Value::Value2(_, env, _, _, _, _, _, _, _)
        | Value::Value3(_, env, _, _, _, _, _, _, _, _, _, _) => {
            rename_env(env, map);
        }
        Value::Value4(l) => {
            rename_loc(l, map);
        }
    }
}

fn rename_el(el: &mut EnvList, map: &HashMap<LOC, LOC>) {
    match el {
        EnvList::EnvList0(el_, _, _, _, v) => {
            rename_el(el_, map);
            rename_value(v, map);
        }
        EnvList::EnvList1(_, _, v) => {
            rename_value(v, map);
        }
    }
}

fn rename_env(env: &mut Env, map: &HashMap<LOC, LOC>) {
    match env {
        Env::Env0(el) => {
            rename_el(el, map);
        }
        Env::Env1() => {}
    }
}

fn rename_ll(ll: &mut LocList, map: &HashMap<LOC, LOC>) {
    match ll {
        LocList::LocList0(ll_, _, l, _, v) => {
            rename_ll(ll_, map);
            rename_loc(l, map);
            rename_value(v, map);
        }
        LocList::LocList1(l, _, v) => {
            rename_loc(l, map);
            rename_value(v, map);
        }
    }
}

fn rename_pres(pres: &mut PreStore, map: &HashMap<LOC, LOC>) {
    match pres {
        PreStore::PreStore0(ll, _) => {
            rename_ll(ll, map);
        }
        PreStore::PreStore1() => {}
    }
}

fn rename_posts(posts: &mut PostStore, map: &HashMap<LOC, LOC>) {
    match posts {
        PostStore::PostStore0(_, ll) => {
            rename_ll(ll, map);
        }
        PostStore::PostStore1() => {}
    }
}

fn rename_loc(l: &mut LOC, map: &HashMap<LOC, LOC>) {
    let l_ = map.get(l).unwrap().clone();
    *l = l_;
}

fn ff(d: &mut Derivation, posts0: &PostStore, posts1: &PostStore) -> io::Result<()> {
    let map = hoge(posts0, posts1)?;
    rename(d, &map);
    Ok(())
}

fn le2e(le: LongExp) -> Exp {
    Exp::Exp0(Box::new(le))
}

fn f2e(f: Fxp) -> Exp {
    Exp::Exp1(Box::new(f))
}

fn g2f(g: Gxp) -> Fxp {
    Fxp::Fxp1(Box::new(g))
}

fn h2g(h: Hxp) -> Gxp {
    Gxp::Gxp1(Box::new(h))
}

fn i2h(i: Ixp) -> Hxp {
    Hxp::Hxp2(Box::new(i))
}

fn j2i(j: Jxp) -> Ixp {
    Ixp::Ixp1(Box::new(j))
}

fn k2j(k: Kxp) -> Jxp {
    Jxp::Jxp1(Box::new(k))
}

fn new_loc() -> LOC {
    LOC::new(&format!("@l{}", common::get_id()))
}

fn push_env(env: &Env, x: &VAR, v: &Value) -> Env {
    match env {
        Env::Env0(el) => Env::Env0(Box::new(EnvList::EnvList0(
            el.clone(),
            Box::new(COMMA::new(",")),
            Box::new(x.clone()),
            Box::new(EQ::new("=")),
            Box::new(v.clone()),
        ))),
        Env::Env1() => Env::Env0(Box::new(EnvList::EnvList1(
            Box::new(x.clone()),
            Box::new(EQ::new("=")),
            Box::new(v.clone()),
        ))),
    }
}

fn push_loc(posts: &PostStore, l: &LOC, v: &Value) -> PostStore {
    match posts {
        PostStore::PostStore0(_, ll) => PostStore::PostStore0(
            Box::new(SLASH::new("/")),
            Box::new(LocList::LocList0(
                ll.clone(),
                Box::new(COMMA::new(",")),
                Box::new(l.clone()),
                Box::new(EQ::new("=")),
                Box::new(v.clone()),
            )),
        ),
        PostStore::PostStore1() => PostStore::PostStore0(
            Box::new(SLASH::new("/")),
            Box::new(LocList::LocList1(
                Box::new(l.clone()),
                Box::new(EQ::new("=")),
                Box::new(v.clone()),
            )),
        ),
    }
}

fn assign(posts: &PostStore, l: &LOC, v: &Value) -> io::Result<PostStore> {
    match posts {
        PostStore::PostStore0(_, ll) => match ll.deref() {
            LocList::LocList0(ll_, _, l_, _, v_) => {
                let posts_ = PostStore::PostStore0(Box::new(SLASH::new("/")), ll_.clone());

                if l == l_.deref() {
                    Ok(push_loc(&posts_, l_, v))
                } else {
                    Ok(push_loc(&assign(&posts_, l, v)?, l_, v_))
                }
            }
            LocList::LocList1(l_, _, _) => {
                if l == l_.deref() {
                    Ok(PostStore::PostStore0(
                        Box::new(SLASH::new("/")),
                        Box::new(LocList::LocList1(
                            l_.clone(),
                            Box::new(EQ::new("=")),
                            Box::new(v.clone()),
                        )),
                    ))
                } else {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!"),
                    ))
                }
            }
        },
        PostStore::PostStore1() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        )),
    }
}

fn get_num(v: &Value) -> io::Result<NUM> {
    if let Value::Value0(n) = v {
        Ok(n.deref().clone())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        ))
    }
}

fn get_truth(v: &Value) -> io::Result<TRUTH> {
    if let Value::Value1(t) = v {
        Ok(t.deref().clone())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        ))
    }
}

fn get_loc(v: &Value) -> io::Result<LOC> {
    if let Value::Value4(l) = v {
        Ok(l.deref().clone())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        ))
    }
}

fn post2pre(s: PostStore) -> PreStore {
    match s {
        PostStore::PostStore0(a, b) => PreStore::PreStore0(b, a),
        PostStore::PostStore1() => PreStore::PreStore1(),
    }
}

fn pre2post(s: PreStore) -> PostStore {
    match s {
        PreStore::PreStore0(a, b) => PostStore::PostStore0(b, a),
        PreStore::PreStore1() => PostStore::PostStore1(),
    }
}

fn eval_exp(pres: &PreStore, env: &Env, e: &Exp) -> io::Result<(Derivation, Value, PostStore)> {
    let (rule, v, posts) = match e {
        Exp::Exp0(le) => {
            return eval_longexp(pres, env, le);
        }
        Exp::Exp1(f) => {
            return eval_fxp(pres, env, f);
        }
        Exp::Exp2(h0, _ /* < */, le1) => {
            let (d0, v0, s0) = eval_hxp(pres, env, h0)?;
            let (d1, v1, s1) = eval_longexp(&post2pre(s0), env, le1)?;
            let (d2, t2) = derive_lt(&get_num(&v0)?, &get_num(&v1)?)?;

            (Rule::ELt(d0, d1, d2), Value::Value1(Box::new(t2)), s1)
        }
        Exp::Exp3(h0, _ /* + */, le1) => {
            let (d0, v0, s0) = eval_hxp(pres, env, h0)?;
            let (d1, v1, s1) = eval_longexp(&post2pre(s0), env, le1)?;
            let (d2, n2) = derive_plus(&get_num(&v0)?, &get_num(&v1)?)?;

            (Rule::EPlus(d0, d1, d2), Value::Value0(Box::new(n2)), s1)
        }
        Exp::Exp4(h0, _ /* - */, le1) => {
            let (d0, v0, s0) = eval_hxp(pres, env, h0)?;
            let (d1, v1, s1) = eval_longexp(&post2pre(s0), env, le1)?;
            let (d2, n2) = derive_minus(&get_num(&v0)?, &get_num(&v1)?)?;

            (Rule::EMinus(d0, d1, d2), Value::Value0(Box::new(n2)), s1)
        }
        Exp::Exp5(i0, _ /* * */, le1) => {
            let (d0, v0, s0) = eval_ixp(pres, env, i0)?;
            let (d1, v1, s1) = eval_longexp(&post2pre(s0), env, le1)?;
            let (d2, n2) = derive_times(&get_num(&v0)?, &get_num(&v1)?)?;

            (Rule::ETimes(d0, d1, d2), Value::Value0(Box::new(n2)), s1)
        }
    };

    let j = Judgement::Judgement0(
        Box::new(pres.clone()),
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(e.clone()),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
        Box::new(posts.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v, posts))
}

fn eval_longexp(
    pres: &PreStore,
    env: &Env,
    le: &LongExp,
) -> io::Result<(Derivation, Value, PostStore)> {
    let (rule, v, posts) = match le {
        LongExp::LongExp0(_, e0, _, e1, _, e2) => {
            let (d0, v0, s1) = eval_exp(pres, env, e0)?;

            if get_truth(&v0)?.as_str() == "true" {
                let (d1, v, s) = eval_exp(&post2pre(s1), env, e1)?;
                (Rule::EIfT(d0, d1), v, s)
            } else {
                let (d1, v, s) = eval_exp(&post2pre(s1), env, e2)?;
                (Rule::EIfF(d0, d1), v, s)
            }
        }

        LongExp::LongExp1(_, x, _, e0, _, e1) => {
            let (d0, v0, s1) = eval_exp(pres, env, e0)?;

            let env_ = match env {
                Env::Env0(el) => Env::Env0(Box::new(EnvList::EnvList0(
                    el.clone(),
                    Box::new(COMMA::new(",")),
                    x.clone(),
                    Box::new(EQ::new("=")),
                    Box::new(v0),
                ))),
                Env::Env1() => Env::Env0(Box::new(EnvList::EnvList1(
                    x.clone(),
                    Box::new(EQ::new("=")),
                    Box::new(v0),
                ))),
            };

            let (d1, v1, s2) = eval_exp(&post2pre(s1), &env_, e1)?;

            (Rule::ELet(d0, d1), v1, s2)
        }

        LongExp::LongExp2(_, x, _, e) => (
            Rule::EFun,
            Value::Value2(
                Box::new(LPAREN::new("(")),
                Box::new(env.clone()),
                Box::new(RPAREN::new(")")),
                Box::new(LBRACKET::new("[")),
                Box::new(FUN::new("fun")),
                x.clone(),
                Box::new(ARROW::new("->")),
                e.clone(),
                Box::new(RBRACKET::new("]")),
            ),
            pre2post(pres.clone()),
        ),

        LongExp::LongExp3(_, _, x, _, _, y, _, e0, _, e1) => {
            let env_ = push_env(
                env,
                x,
                &Value::Value3(
                    Box::new(LPAREN::new("(")),
                    Box::new(env.clone()),
                    Box::new(RPAREN::new(")")),
                    Box::new(LBRACKET::new("[")),
                    Box::new(REC::new("rec")),
                    x.clone(),
                    Box::new(EQ::new("=")),
                    Box::new(FUN::new("fun")),
                    y.clone(),
                    Box::new(ARROW::new("->")),
                    e0.clone(),
                    Box::new(RBRACKET::new("]")),
                ),
            );

            let (d0, v0, s0) = eval_exp(pres, &env_, e1)?;

            (Rule::ELetRec(d0), v0, s0)
        }
    };

    let j = Judgement::Judgement0(
        Box::new(pres.clone()),
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(le2e(le.clone())),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
        Box::new(posts.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v, posts))
}

fn eval_fxp(pres: &PreStore, env: &Env, f: &Fxp) -> io::Result<(Derivation, Value, PostStore)> {
    let (rule, v, posts) = match f {
        Fxp::Fxp0(g0, _ /* := */, f1) => {
            let (d0, v0, s0) = eval_gxp(pres, env, g0)?;
            let (d1, v1, s1) = eval_fxp(&post2pre(s0), env, f1)?;

            let l = get_loc(&v0)?;
            let s_ = assign(&s1, &l, &v1)?;

            (Rule::EAssign(d0, d1), v1, s_)
        }

        Fxp::Fxp1(g0) => {
            return eval_gxp(pres, env, g0);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(pres.clone()),
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(f.clone())),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
        Box::new(posts.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v, posts))
}

fn eval_gxp(pres: &PreStore, env: &Env, g: &Gxp) -> io::Result<(Derivation, Value, PostStore)> {
    let (rule, v, posts) = match g {
        Gxp::Gxp0(h0, _ /* < */, h1) => {
            let (d0, v0, s0) = eval_hxp(pres, env, h0)?;
            let (d1, v1, s1) = eval_hxp(&post2pre(s0), env, h1)?;
            let (d2, t2) = derive_lt(&get_num(&v0)?, &get_num(&v1)?)?;

            (Rule::ELt(d0, d1, d2), Value::Value1(Box::new(t2)), s1)
        }

        Gxp::Gxp1(h0) => {
            return eval_hxp(pres, env, h0);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(pres.clone()),
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(g.clone()))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
        Box::new(posts.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v, posts))
}

fn eval_hxp(pres: &PreStore, env: &Env, h: &Hxp) -> io::Result<(Derivation, Value, PostStore)> {
    let (rule, v, posts) = match h {
        Hxp::Hxp0(h0, _ /* + */, i1) => {
            let (d0, v0, s0) = eval_hxp(pres, env, h0)?;
            let (d1, v1, s1) = eval_ixp(&post2pre(s0), env, i1)?;
            let (d2, n2) = derive_plus(&get_num(&v0)?, &get_num(&v1)?)?;

            (Rule::EPlus(d0, d1, d2), Value::Value0(Box::new(n2)), s1)
        }

        Hxp::Hxp1(h0, _ /* - */, i1) => {
            let (d0, v0, s0) = eval_hxp(pres, env, h0)?;
            let (d1, v1, s1) = eval_ixp(&post2pre(s0), env, i1)?;
            let (d2, n2) = derive_minus(&get_num(&v0)?, &get_num(&v1)?)?;

            (Rule::EMinus(d0, d1, d2), Value::Value0(Box::new(n2)), s1)
        }

        Hxp::Hxp2(i0) => {
            return eval_ixp(pres, env, i0);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(pres.clone()),
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(h.clone())))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
        Box::new(posts.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v, posts))
}

fn eval_ixp(pres: &PreStore, env: &Env, i: &Ixp) -> io::Result<(Derivation, Value, PostStore)> {
    let (rule, v, posts) = match i {
        Ixp::Ixp0(i0, _ /* * */, j1) => {
            let (d0, v0, s0) = eval_ixp(pres, env, i0)?;
            let (d1, v1, s1) = eval_jxp(&post2pre(s0), env, j1)?;
            let (d2, n2) = derive_times(&get_num(&v0)?, &get_num(&v1)?)?;

            (Rule::ETimes(d0, d1, d2), Value::Value0(Box::new(n2)), s1)
        }

        Ixp::Ixp1(j0) => {
            return eval_jxp(pres, env, j0);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(pres.clone()),
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(i.clone()))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
        Box::new(posts.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v, posts))
}

fn eval_jxp(pres: &PreStore, env: &Env, j: &Jxp) -> io::Result<(Derivation, Value, PostStore)> {
    let (rule, v, posts) = match j {
        Jxp::Jxp0(j0, k1) => {
            let (d0, v0, s0) = eval_jxp(pres, env, j0)?;
            let (d1, v1, s1) = eval_kxp(&post2pre(s0), env, k1)?;

            match &v0 {
                Value::Value2(_, env1, _, _, _, x, _, e0, _) => {
                    let env_ = push_env(env1, x, &v1);
                    let (d2, v2, s2) = eval_exp(&post2pre(s1), &env_, &e0)?;
                    (Rule::EApp(d0, d1, d2), v2, s2)
                }
                Value::Value3(_, env1, _, _, _, x, _, _, y, _, e0, _) => {
                    let env_ = push_env(&push_env(env1, x, &v0), y, &v1);
                    let (d2, v2, s2) = eval_exp(&post2pre(s1), &env_, e0)?;
                    (Rule::EAppRec(d0, d1, d2), v2, s2)
                }
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!"),
                    ));
                }
            }
        }

        Jxp::Jxp1(k0) => {
            return eval_kxp(pres, env, k0);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(pres.clone()),
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(j.clone())))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
        Box::new(posts.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v, posts))
}

fn eval_kxp(pres: &PreStore, env: &Env, k: &Kxp) -> io::Result<(Derivation, Value, PostStore)> {
    let (rule, v, posts) = match k {
        Kxp::Kxp0(n) => (Rule::EInt, Value::Value0(n.clone()), pre2post(pres.clone())),
        Kxp::Kxp1(t) => (
            Rule::EBool,
            Value::Value1(t.clone()),
            pre2post(pres.clone()),
        ),
        Kxp::Kxp2(x) => (Rule::EVar, find_var(env, x)?, pre2post(pres.clone())),
        Kxp::Kxp3(_ /* ref */, k0) => {
            let (d0, v0, s0) = eval_kxp(pres, env, k0)?;

            let l = new_loc();
            let s_ = push_loc(&s0, &l, &v0);

            (Rule::ERef(d0), Value::Value4(Box::new(l)), s_)
        }
        Kxp::Kxp4(_ /* deref */, k0) => {
            let (d0, v0, s0) = eval_kxp(pres, env, k0)?;
            (Rule::EDeref(d0), find_loc(&s0, &get_loc(&v0)?)?, s0)
        }
        Kxp::Kxp5(_, e0, _) => {
            return eval_exp(pres, env, e0);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(pres.clone()),
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(k2j(k.clone()))))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
        Box::new(posts.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v, posts))
}

fn find_var(env: &Env, x: &VAR) -> io::Result<Value> {
    match env {
        Env::Env0(el) => match el.deref() {
            EnvList::EnvList0(el_, _, y, _, v) => {
                if x == y.deref() {
                    Ok(v.deref().clone())
                } else {
                    find_var(&Env::Env0(el_.clone()), x)
                }
            }
            EnvList::EnvList1(y, _, v) => {
                if x == y.deref() {
                    Ok(v.deref().clone())
                } else {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!"),
                    ))
                }
            }
        },

        Env::Env1() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        )),
    }
}

fn find_loc(s: &PostStore, l: &LOC) -> io::Result<Value> {
    match s {
        PostStore::PostStore0(_, ll) => match ll.deref() {
            LocList::LocList0(ll_, _, l_, _, v) => {
                if l == l_.deref() {
                    Ok(v.deref().clone())
                } else {
                    find_loc(
                        &PostStore::PostStore0(Box::new(SLASH::new("/")), ll_.clone()),
                        l,
                    )
                }
            }
            LocList::LocList1(l_, _, v) => {
                if l == l_.deref() {
                    Ok(v.deref().clone())
                } else {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!"),
                    ))
                }
            }
        },
        PostStore::PostStore1() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        )),
    }
}

fn derive_plus(n0: &NUM, n1: &NUM) -> io::Result<(Derivation, NUM)> {
    let i0: i32 = n0.as_str().parse().unwrap();
    let i1: i32 = n1.as_str().parse().unwrap();
    let n2 = NUM::new(&(i0 + i1).to_string());

    let j = Judgement::Judgement1(
        Box::new(n0.clone()),
        Box::new(PLUS::new("plus")),
        Box::new(n1.clone()),
        Box::new(IS::new("is")),
        Box::new(n2.clone()),
    );

    Ok((Derivation(j, Box::new(Rule::BPlus)), n2))
}

fn derive_minus(n0: &NUM, n1: &NUM) -> io::Result<(Derivation, NUM)> {
    let i0: i32 = n0.as_str().parse().unwrap();
    let i1: i32 = n1.as_str().parse().unwrap();
    let n2 = NUM::new(&(i0 - i1).to_string());

    let j = Judgement::Judgement2(
        Box::new(n0.clone()),
        Box::new(MINUS::new("minus")),
        Box::new(n1.clone()),
        Box::new(IS::new("is")),
        Box::new(n2.clone()),
    );

    Ok((Derivation(j, Box::new(Rule::BMinus)), n2))
}

fn derive_times(n0: &NUM, n1: &NUM) -> io::Result<(Derivation, NUM)> {
    let i0: i32 = n0.as_str().parse().unwrap();
    let i1: i32 = n1.as_str().parse().unwrap();
    let n2 = NUM::new(&(i0 * i1).to_string());

    let j = Judgement::Judgement3(
        Box::new(n0.clone()),
        Box::new(TIMES::new("times")),
        Box::new(n1.clone()),
        Box::new(IS::new("is")),
        Box::new(n2.clone()),
    );

    Ok((Derivation(j, Box::new(Rule::BTimes)), n2))
}

fn derive_lt(n0: &NUM, n1: &NUM) -> io::Result<(Derivation, TRUTH)> {
    let i0: i32 = n0.as_str().parse().unwrap();
    let i1: i32 = n1.as_str().parse().unwrap();
    let t2 = TRUTH::new(&(i0 < i1).to_string());

    let j = Judgement::Judgement4(
        Box::new(n0.clone()),
        Box::new(LESS::new("less")),
        Box::new(THAN::new("than")),
        Box::new(n1.clone()),
        Box::new(IS::new("is")),
        Box::new(t2.clone()),
    );

    Ok((Derivation(j, Box::new(Rule::BLt)), t2))
}

fn derive(j: &Judgement) -> io::Result<Derivation> {
    match &j {
        Judgement::Judgement0(pres, env, _, e, _, v, posts) => {
            let (mut d, v_, posts_) = eval_exp(pres, env, e)?;

            ff(&mut d, &posts_, posts)?;

            if v.deref() == &v_ {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement1(n0, _ /* plus */, n1, _, n2) => {
            let (d, n2_) = derive_plus(n0, n1)?;
            if n2.deref() == &n2_ {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement2(n0, _ /* minus */, n1, _, n2) => {
            let (d, n2_) = derive_minus(n0, n1)?;
            if n2.deref() == &n2_ {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement3(n0, _ /* times */, n1, _, n2) => {
            let (d, n2_) = derive_times(n0, n1)?;
            if n2.deref() == &n2_ {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement4(n0, _ /* less */, _ /* than */, n1, _, t2) => {
            let (d, t2_) = derive_lt(n0, n1)?;
            if t2.deref() == &t2_ {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }
    }
}

pub fn f(s: &str) -> io::Result<String> {
    match Parser::parse(s) {
        Ok(j) => {
            let d = derive(&j)?;
            Ok(format!("{}", d))
        }
        Err(s) => Err(io::Error::new(io::ErrorKind::InvalidInput, s)),
    }
}
