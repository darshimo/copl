mod rule;

use std::{collections::HashSet, io, ops::Deref};

use self::rule::{
    Clauses, Element, Env, EnvList, Exp, Fxp, Gxp, Hxp, Ixp, Judgement, Jxp, Kxp, LongExp, Parser,
    Pat, SubPat, Value, ARROW, COMMA, CONS, DOESNT, EQ, EVALTO, FUN, IS, LBRACKET, LESS, LPAREN,
    MATCH, MATCHES, MINUS, NUM, PLUS, RBRACKET, REC, RPAREN, THAN, TIMES, TRUTH, VAR, VDASH, WHEN,
    WITH,
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
    MVar,
    MNil,
    MCons(Derivation, Derivation),
    MWild,
    NMConsNil,
    NMNilCons,
    NMConsConsL(Derivation),
    NMConsConsR(Derivation),
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
    ENil,
    ECons(Derivation, Derivation),
    EMatchM1(Derivation, Derivation, Derivation),
    EMatchM2(Derivation, Derivation, Derivation),
    EMatchN(Derivation, Derivation, Derivation),
    BPlus,
    BMinus,
    BTimes,
    BLt,
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::MVar => write!(f, "M-Var {{}}"),
            Rule::MNil => write!(f, "M-Nil {{}}"),
            Rule::MCons(d0, d1) => write!(f, "M-Cons {{{};{}}}", d0, d1),
            Rule::MWild => write!(f, "M-Wild {{}}"),
            Rule::NMConsNil => write!(f, "NM-ConsNil {{}}"),
            Rule::NMNilCons => write!(f, "NM-NilCons {{}}"),
            Rule::NMConsConsL(d0) => write!(f, "NM-ConsConsL {{{}}}", d0),
            Rule::NMConsConsR(d0) => write!(f, "NM-ConsConsR {{{}}}", d0),
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
            Rule::ENil => write!(f, "E-Nil {{}}"),
            Rule::ECons(d0, d1) => write!(f, "E-Cons {{{};{}}}", d0, d1),
            Rule::EMatchM1(d0, d1, d2) => write!(f, "E-MatchM1 {{{};{};{}}}", d0, d1, d2),
            Rule::EMatchM2(d0, d1, d2) => write!(f, "E-MatchM2 {{{};{};{}}}", d0, d1, d2),
            Rule::EMatchN(d0, d1, d2) => write!(f, "E-MatchN {{{};{};{}}}", d0, d1, d2),
            Rule::BPlus => write!(f, "B-Plus {{}}"),
            Rule::BMinus => write!(f, "B-Minus {{}}"),
            Rule::BTimes => write!(f, "B-Times {{}}"),
            Rule::BLt => write!(f, "B-Lt {{}}"),
        }
    }
}

fn f2e(f: Fxp) -> Exp {
    Exp::Exp1(Box::new(f))
}

fn g2e(g: Gxp) -> Exp {
    f2e(Fxp::Fxp1(Box::new(g)))
}

fn h2e(h: Hxp) -> Exp {
    g2e(Gxp::Gxp1(Box::new(h)))
}

fn i2e(i: Ixp) -> Exp {
    h2e(Hxp::Hxp2(Box::new(i)))
}

fn j2e(j: Jxp) -> Exp {
    i2e(Ixp::Ixp1(Box::new(j)))
}

fn k2e(k: Kxp) -> Exp {
    j2e(Jxp::Jxp1(Box::new(k)))
}

fn merge_env(env0: &Env, env1: &Env, prime_demand: bool) -> io::Result<Env> {
    if prime_demand && get_vars(env0).intersection(&get_vars(env1)).count() > 0 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        ));
    }

    match env1 {
        Env::Env0(el) => match el.deref() {
            EnvList::EnvList0(el_, _, x, _, v) => {
                let env1_ = Env::Env0(el_.clone());
                let ret = merge_env(env0, &env1_, false)?;
                Ok(push_env(&ret, x, v))
            }

            EnvList::EnvList1(x, _, v) => Ok(push_env(env0, x, v)),
        },

        Env::Env1() => Ok(env0.clone()),
    }
}

fn get_vars(env: &Env) -> HashSet<String> {
    match env {
        Env::Env0(el) => match el.deref() {
            EnvList::EnvList0(el_, _, x, _, _) => {
                let mut set = get_vars(&Env::Env0(el_.clone()));
                set.insert(x.as_str().to_string());
                set
            }
            EnvList::EnvList1(x, _, _) => HashSet::from([x.as_str().to_string()]),
        },
        Env::Env1() => HashSet::new(),
    }
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

fn cons(v0: &Value, v1: &Value) -> Value {
    match v0 {
        Value::Value0(_, _, _) => Value::Value0(
            Box::new(Element::Element5(
                Box::new(LPAREN::new("(")),
                Box::new(v0.clone()),
                Box::new(RPAREN::new(")")),
            )),
            Box::new(CONS::new("::")),
            Box::new(v1.clone()),
        ),
        Value::Value1(elem) => Value::Value0(
            elem.clone(),
            Box::new(CONS::new("::")),
            Box::new(v1.clone()),
        ),
    }
}

fn pop(v: &Value) -> io::Result<Option<(Value, Value)>> {
    match v {
        Value::Value0(elem, _, v1) => Ok(Some((Value::Value1(elem.clone()), v1.deref().clone()))),
        Value::Value1(elem) => match elem.deref() {
            Element::Element4(_, _) => Ok(None),
            Element::Element5(_, v_, _) => pop(v_),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("DerivationError!"),
            )),
        },
    }
}

fn get_num(v: &Value) -> io::Result<i32> {
    if let Value::Value1(elem) = v {
        if let Element::Element0(n) = elem.deref() {
            return Ok(n.as_str().parse().unwrap());
        }
    }

    Err(io::Error::new(
        io::ErrorKind::InvalidInput,
        format!("DerivationError!"),
    ))
}

fn get_truth(v: &Value) -> io::Result<bool> {
    if let Value::Value1(elem) = v {
        if let Element::Element1(t) = elem.deref() {
            return Ok(t.as_str().parse().unwrap());
        }
    }

    Err(io::Error::new(
        io::ErrorKind::InvalidInput,
        format!("DerivationError!"),
    ))
}

fn eval_exp(env: &Env, e: &Exp) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match e {
        Exp::Exp0(le) => {
            return eval_longexp(env, le);
        }
        Exp::Exp1(f) => {
            return eval_fxp(env, f);
        }
        Exp::Exp2(g, _ /* < */, le) => {
            let (d0, v0) = eval_gxp(env, g)?;
            let (d1, v1) = eval_longexp(env, le)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, t) = derive_lt(&n0, &n1)?;

            let rule = Rule::ELt(d0, d1, d2);
            let v = Value::Value1(Box::new(Element::Element1(Box::new(t))));

            (rule, v)
        }
        Exp::Exp3(h, _ /* :: */, le) => {
            let (d0, v0) = eval_hxp(env, h)?;
            let (d1, v1) = eval_longexp(env, le)?;

            let v = cons(&v0, &v1);

            (Rule::ECons(d0, d1), v)
        }
        Exp::Exp4(h, _ /* + */, le) => {
            let (d0, v0) = eval_hxp(env, h)?;
            let (d1, v1) = eval_longexp(env, le)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_plus(&n0, &n1)?;

            (
                Rule::EPlus(d0, d1, d2),
                Value::Value1(Box::new(Element::Element0(Box::new(n)))),
            )
        }
        Exp::Exp5(h, _ /* - */, le) => {
            let (d0, v0) = eval_hxp(env, h)?;
            let (d1, v1) = eval_longexp(env, le)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_minus(&n0, &n1)?;

            (
                Rule::EMinus(d0, d1, d2),
                Value::Value1(Box::new(Element::Element0(Box::new(n)))),
            )
        }
        Exp::Exp6(i, _ /* * */, le) => {
            let (d0, v0) = eval_ixp(env, i)?;
            let (d1, v1) = eval_longexp(env, le)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_times(&n0, &n1)?;

            (
                Rule::ETimes(d0, d1, d2),
                Value::Value1(Box::new(Element::Element0(Box::new(n)))),
            )
        }
    };

    let j = Judgement::Judgement0(
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(e.clone()),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_longexp(env: &Env, le: &LongExp) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match le {
        LongExp::LongExp0(_, e0, _, e1, _, e2) => {
            let (d0, v0) = eval_exp(env, e0)?;

            if get_truth(&v0)? {
                let (d1, v) = eval_exp(env, e1)?;
                (Rule::EIfT(d0, d1), v)
            } else {
                let (d1, v) = eval_exp(env, e2)?;
                (Rule::EIfF(d0, d1), v)
            }
        }

        LongExp::LongExp1(_, x, _, e0, _, e1) => {
            let (d0, v0) = eval_exp(env, e0)?;

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

            let (d1, v1) = eval_exp(&env_, e1)?;

            (Rule::ELet(d0, d1), v1)
        }

        LongExp::LongExp2(_, x, _, e) => (
            Rule::EFun,
            Value::Value1(Box::new(Element::Element2(
                Box::new(LPAREN::new("(")),
                Box::new(env.clone()),
                Box::new(RPAREN::new(")")),
                Box::new(LBRACKET::new("[")),
                Box::new(FUN::new("fun")),
                x.clone(),
                Box::new(ARROW::new("->")),
                e.clone(),
                Box::new(RBRACKET::new("]")),
            ))),
        ),

        LongExp::LongExp3(_, _, x, _, _, y, _, e0, _, e1) => {
            let env_ = push_env(
                env,
                x,
                &Value::Value1(Box::new(Element::Element3(
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
                ))),
            );

            let (d0, v0) = eval_exp(&env_, e1)?;

            (Rule::ELetRec(d0), v0)
        }

        LongExp::LongExp4(_, e, _, c) => match c.deref() {
            Clauses::Clauses0(p, _, e_, _, c_) => {
                let (d0, v0) = eval_exp(env, e)?;
                let (d1, op) = eval_pat(p, &v0)?;
                if let Some(env1) = op {
                    let env2 = merge_env(env, &env1, false)?;
                    let (d2, v1) = eval_exp(&env2, e_)?;

                    (Rule::EMatchM2(d0, d1, d2), v1)
                } else {
                    let (d2, v2) = eval_exp(
                        env,
                        &Exp::Exp0(Box::new(LongExp::LongExp4(
                            Box::new(MATCH::new("match")),
                            e.clone(),
                            Box::new(WITH::new("with")),
                            c_.clone(),
                        ))),
                    )?;

                    (Rule::EMatchN(d0, d1, d2), v2)
                }
            }

            Clauses::Clauses1(p, _, e_) => {
                let (d0, v0) = eval_exp(env, e)?;
                let (d1, op) = eval_pat(p, &v0)?;
                if let Some(env1) = op {
                    let env2 = merge_env(env, &env1, false)?;
                    let (d2, v1) = eval_exp(&env2, e_)?;

                    (Rule::EMatchM1(d0, d1, d2), v1)
                } else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!"),
                    ));
                }
            }
        },
    };

    let j = Judgement::Judgement0(
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(Exp::Exp0(Box::new(le.clone()))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_fxp(env: &Env, f: &Fxp) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match f {
        Fxp::Fxp0(g0, _ /* < */, g1) => {
            let (d0, v0) = eval_gxp(env, g0)?;
            let (d1, v1) = eval_gxp(env, g1)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, t) = derive_lt(&n0, &n1)?;

            (
                Rule::ELt(d0, d1, d2),
                Value::Value1(Box::new(Element::Element1(Box::new(t)))),
            )
        }

        Fxp::Fxp1(g) => {
            return eval_gxp(env, g);
        }
    };

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(Exp::Exp1(Box::new(f.clone()))),
                Box::new(EVALTO::new("evalto")),
                Box::new(v.clone()),
            ),
            Box::new(rule),
        ),
        v,
    ))
}

fn eval_gxp(env: &Env, g: &Gxp) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match g {
        Gxp::Gxp0(h, _ /* :: */, g) => {
            let (d0, v0) = eval_hxp(env, h)?;
            let (d1, v1) = eval_gxp(env, g)?;

            let v = cons(&v0, &v1);

            (Rule::ECons(d0, d1), v)
        }

        Gxp::Gxp1(h) => {
            return eval_hxp(env, h);
        }
    };

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(Exp::Exp1(Box::new(Fxp::Fxp1(Box::new(g.clone()))))),
                Box::new(EVALTO::new("evalto")),
                Box::new(v.clone()),
            ),
            Box::new(rule),
        ),
        v,
    ))
}

fn eval_hxp(env: &Env, h: &Hxp) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match h {
        Hxp::Hxp0(h, _ /* + */, i) => {
            let (d0, v0) = eval_hxp(env, h)?;
            let (d1, v1) = eval_ixp(env, i)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_plus(&n0, &n1)?;

            (
                Rule::EPlus(d0, d1, d2),
                Value::Value1(Box::new(Element::Element0(Box::new(n)))),
            )
        }

        Hxp::Hxp1(h, _ /* - */, i) => {
            let (d0, v0) = eval_hxp(env, h)?;
            let (d1, v1) = eval_ixp(env, i)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_minus(&n0, &n1)?;

            (
                Rule::EMinus(d0, d1, d2),
                Value::Value1(Box::new(Element::Element0(Box::new(n)))),
            )
        }

        Hxp::Hxp2(i) => {
            return eval_ixp(env, i);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(Exp::Exp1(Box::new(Fxp::Fxp1(Box::new(Gxp::Gxp1(
            Box::new(h.clone()),
        )))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_ixp(env: &Env, i: &Ixp) -> io::Result<(Derivation, Value)> {
    let ((d0, v0), (d1, v1)) = match i {
        Ixp::Ixp0(i, _, j) => (eval_ixp(env, i)?, eval_jxp(env, j)?),

        Ixp::Ixp1(j) => {
            return eval_jxp(env, j);
        }
    };

    let i0 = get_num(&v0)?;
    let i1 = get_num(&v1)?;
    let n0 = NUM::new(&i0.to_string());
    let n1 = NUM::new(&i1.to_string());

    let (d2, n) = derive_times(&n0, &n1)?;

    let rule = Rule::ETimes(d0, d1, d2);
    let v = Value::Value1(Box::new(Element::Element0(Box::new(n))));

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(Exp::Exp1(Box::new(Fxp::Fxp1(Box::new(Gxp::Gxp1(
                    Box::new(Hxp::Hxp2(Box::new(i.clone()))),
                )))))),
                Box::new(EVALTO::new("evalto")),
                Box::new(v.clone()),
            ),
            Box::new(rule),
        ),
        v,
    ))
}

fn eval_jxp(env: &Env, j: &Jxp) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match j {
        Jxp::Jxp0(j0, k1) => {
            let (d0, v0) = eval_jxp(env, j0)?;
            let (d1, v1) = eval_kxp(env, k1)?;

            match &v0 {
                Value::Value1(elem) => match elem.deref() {
                    Element::Element2(_, env2, _, _, _, x, _, e0, _) => {
                        let env_ = push_env(env2, x, &v1);

                        let (d2, v2) = eval_exp(&env_, &e0)?;

                        (Rule::EApp(d0, d1, d2), v2)
                    }

                    Element::Element3(_, env2, _, _, _, x, _, _, y, _, e0, _) => {
                        let env_ = push_env(&push_env(env2, x, &v0), y, &v1);

                        let (d2, v2) = eval_exp(&env_, &e0)?;

                        (Rule::EAppRec(d0, d1, d2), v2)
                    }

                    _ => {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            format!("DerivationError!"),
                        ));
                    }
                },

                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!"),
                    ));
                }
            }
        }
        Jxp::Jxp1(k) => {
            return eval_kxp(env, k);
        }
    };

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(Exp::Exp1(Box::new(Fxp::Fxp1(Box::new(Gxp::Gxp1(
                    Box::new(Hxp::Hxp2(Box::new(Ixp::Ixp1(Box::new(j.clone()))))),
                )))))),
                Box::new(EVALTO::new("evalto")),
                Box::new(v.clone()),
            ),
            Box::new(rule),
        ),
        v,
    ))
}

fn eval_kxp(env: &Env, k: &Kxp) -> io::Result<(Derivation, Value)> {
    match k {
        Kxp::Kxp0(n) => eval_num(env, n),
        Kxp::Kxp1(t) => eval_truth(env, t),
        Kxp::Kxp2(x) => eval_env(env, x),
        Kxp::Kxp3(_, _) => {
            let v = Value::Value1(Box::new(Element::Element4(
                Box::new(LBRACKET::new("[")),
                Box::new(RBRACKET::new("]")),
            )));
            let j = Judgement::Judgement0(
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(Exp::Exp1(Box::new(Fxp::Fxp1(Box::new(Gxp::Gxp1(
                    Box::new(Hxp::Hxp2(Box::new(Ixp::Ixp1(Box::new(Jxp::Jxp1(
                        Box::new(Kxp::Kxp3(
                            Box::new(LBRACKET::new("[")),
                            Box::new(RBRACKET::new("]")),
                        )),
                    )))))),
                )))))),
                Box::new(EVALTO::new("evalto")),
                Box::new(v.clone()),
            );
            Ok((Derivation(j, Box::new(Rule::ENil)), v))
        }
        Kxp::Kxp4(_, e, _) => eval_exp(env, e),
    }
}

fn eval_envlist(el: &EnvList, x: &VAR) -> io::Result<Value> {
    match el {
        EnvList::EnvList0(el_, _, y, _, v) => {
            if x == y.deref() {
                Ok(v.deref().clone())
            } else {
                eval_envlist(el_, x)
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
    }
}

fn eval_env(env: &Env, x: &VAR) -> io::Result<(Derivation, Value)> {
    match env {
        Env::Env0(el) => {
            let v = eval_envlist(el, x)?;
            let j = Judgement::Judgement0(
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(k2e(Kxp::Kxp2(Box::new(x.clone())))),
                Box::new(EVALTO::new("evalto")),
                Box::new(v.clone()),
            );
            Ok((Derivation(j, Box::new(Rule::EVar)), v))
        }

        Env::Env1() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        )),
    }
}

fn eval_num(env: &Env, n: &NUM) -> io::Result<(Derivation, Value)> {
    let v = Value::Value1(Box::new(Element::Element0(Box::new(n.clone()))));

    let j = Judgement::Judgement0(
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(k2e(Kxp::Kxp0(Box::new(n.clone())))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
    );

    Ok((Derivation(j, Box::new(Rule::EInt)), v))
}

fn eval_truth(env: &Env, t: &TRUTH) -> io::Result<(Derivation, Value)> {
    let v = Value::Value1(Box::new(Element::Element1(Box::new(t.clone()))));

    let j = Judgement::Judgement0(
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(k2e(Kxp::Kxp1(Box::new(t.clone())))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
    );

    Ok((Derivation(j, Box::new(Rule::EBool)), v))
}

fn eval_pat(p: &Pat, v: &Value) -> io::Result<(Derivation, Option<Env>)> {
    let (rule, op) = match p {
        Pat::Pat0(sp, _, p_) => match v {
            Value::Value0(elem, _, v_) => {
                let (d0, op0) = eval_pat(&Pat::Pat1(sp.clone()), &Value::Value1(elem.clone()))?;

                if let Some(env0) = op0 {
                    let (d1, op1) = eval_pat(p_, v_)?;

                    if let Some(env1) = op1 {
                        let env = merge_env(&env0, &env1, true)?;

                        (Rule::MCons(d0, d1), Some(env))
                    } else {
                        (Rule::NMConsConsR(d1), None)
                    }
                } else {
                    (Rule::NMConsConsL(d0), None)
                }
            }

            Value::Value1(elem) => match elem.deref() {
                Element::Element4(_, _) => (Rule::NMNilCons, None),
                Element::Element5(_, v_, _) => {
                    return eval_pat(p, v_);
                }
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!"),
                    ));
                }
            },
        },

        Pat::Pat1(sp) => match sp.deref() {
            SubPat::SubPat0(x) => (
                Rule::MVar,
                Some(Env::Env0(Box::new(EnvList::EnvList1(
                    x.clone(),
                    Box::new(EQ::new("=")),
                    Box::new(v.clone()),
                )))),
            ),
            SubPat::SubPat1(_, _) => match v {
                Value::Value0(_, _, _) => (Rule::NMConsNil, None),
                Value::Value1(elem) => match elem.deref() {
                    Element::Element4(_, _) => (Rule::MNil, Some(Env::Env1())),
                    Element::Element5(_, v_, _) => {
                        return eval_pat(p, v_);
                    }
                    _ => {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            format!("DerivationError!"),
                        ));
                    }
                },
            },
            SubPat::SubPat2(_) => (Rule::MWild, Some(Env::Env1())),
            SubPat::SubPat3(_, p_, _) => {
                return eval_pat(p_, v);
            }
        },
    };

    let j = if let Some(env) = &op {
        Judgement::Judgement5(
            Box::new(p.clone()),
            Box::new(MATCHES::new("matches")),
            Box::new(v.clone()),
            Box::new(WHEN::new("when")),
            Box::new(LPAREN::new("(")),
            Box::new(env.clone()),
            Box::new(RPAREN::new(")")),
        )
    } else {
        Judgement::Judgement6(
            Box::new(p.clone()),
            Box::new(DOESNT::new("doesn't")),
            Box::new(MATCH::new("match")),
            Box::new(v.clone()),
        )
    };

    Ok((Derivation(j, Box::new(rule)), op))
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
        Judgement::Judgement0(env, _, e, _, r) => {
            let (d, r_) = eval_exp(env, e)?;
            if r.deref() == &r_ {
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

        Judgement::Judgement5(p, _, v, _, _, env, _) => {
            let (d, env_) = eval_pat(p, v)?;
            if Some(env.deref()) == env_.as_ref() {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement6(p, _, _, v) => {
            let (d, env_) = eval_pat(p, v)?;
            if env_ == None {
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
