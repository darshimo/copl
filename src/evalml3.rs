mod rule;

use std::{io, ops::Deref};

use self::rule::{
    Env, EnvList, Exp, Fxp, Gxp, Hxp, Ixp, Judgement, Jxp, LongExp, Parser, Value, ARROW, COMMA,
    EQ, EVALTO, FUN, IS, LBRACKET, LESS, LPAREN, MINUS, NUM, PLUS, RBRACKET, REC, RPAREN, THAN,
    TIMES, TRUTH, VAR, VDASH,
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
    EVar1,
    EVar2(Derivation),
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
            Rule::EVar1 => write!(f, "E-Var1 {{}}"),
            Rule::EVar2(d0) => write!(f, "E-Var2 {{{}}}", d0),
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
            Rule::BPlus => write!(f, "B-Plus {{}}"),
            Rule::BMinus => write!(f, "B-Minus {{}}"),
            Rule::BTimes => write!(f, "B-Times {{}}"),
            Rule::BLt => write!(f, "B-Lt {{}}"),
        }
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

fn get_num(v: &Value) -> io::Result<i32> {
    if let Value::Value0(n) = v {
        Ok(n.as_str().parse().unwrap())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        ))
    }
}

fn get_truth(v: &Value) -> io::Result<bool> {
    if let Value::Value1(t) = v {
        Ok(t.as_str().parse().unwrap())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        ))
    }
}

fn eval_exp(env: &Env, e: &Exp) -> io::Result<(Derivation, Value)> {
    match e {
        Exp::Exp0(le) => eval_longexp(env, le),
        Exp::Exp1(f) => eval_fxp(env, f),
    }
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

            let (d0, v0) = eval_exp(&env_, e1)?;

            (Rule::ELetRec(d0), v0)
        }
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
    let ((d0, v0), (d1, v1)) = match f {
        Fxp::Fxp0(g, _ /* < */, le) => (eval_gxp(env, g)?, eval_longexp(env, le)?),

        Fxp::Fxp1(g0, _ /* < */, g1) => (eval_gxp(env, g0)?, eval_gxp(env, g1)?),

        Fxp::Fxp2(g) => {
            return eval_gxp(env, g);
        }
    };

    let i0 = get_num(&v0)?;
    let i1 = get_num(&v1)?;
    let n0 = NUM::new(&i0.to_string());
    let n1 = NUM::new(&i1.to_string());

    let (d2, t) = derive_lt(&n0, &n1)?;

    let rule = Rule::ELt(d0, d1, d2);
    let v = Value::Value1(Box::new(t));

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
        Gxp::Gxp0(g, _ /* + */, le) => {
            let (d0, v0) = eval_gxp(env, g)?;
            let (d1, v1) = eval_longexp(env, le)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_plus(&n0, &n1)?;

            (Rule::EPlus(d0, d1, d2), Value::Value0(Box::new(n)))
        }

        Gxp::Gxp1(g, _ /* - */, le) => {
            let (d0, v0) = eval_gxp(env, g)?;
            let (d1, v1) = eval_longexp(env, le)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_minus(&n0, &n1)?;

            (Rule::EMinus(d0, d1, d2), Value::Value0(Box::new(n)))
        }

        Gxp::Gxp2(g, _ /* + */, h) => {
            let (d0, v0) = eval_gxp(env, g)?;
            let (d1, v1) = eval_hxp(env, h)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_plus(&n0, &n1)?;

            (Rule::EPlus(d0, d1, d2), Value::Value0(Box::new(n)))
        }

        Gxp::Gxp3(g, _ /* - */, h) => {
            let (d0, v0) = eval_gxp(env, g)?;
            let (d1, v1) = eval_hxp(env, h)?;

            let i0 = get_num(&v0)?;
            let i1 = get_num(&v1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_minus(&n0, &n1)?;

            (Rule::EMinus(d0, d1, d2), Value::Value0(Box::new(n)))
        }

        Gxp::Gxp4(h) => {
            return eval_hxp(env, h);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(Exp::Exp1(Box::new(Fxp::Fxp2(Box::new(g.clone()))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_hxp(env: &Env, h: &Hxp) -> io::Result<(Derivation, Value)> {
    let ((d0, v0), (d1, v1)) = match h {
        Hxp::Hxp0(h, _ /* * */, le) => (eval_hxp(env, h)?, eval_longexp(env, le)?),

        Hxp::Hxp1(h, _, i) => (eval_hxp(env, h)?, eval_ixp(env, i)?),

        Hxp::Hxp2(i) => {
            return eval_ixp(env, i);
        }
    };

    let i0 = get_num(&v0)?;
    let i1 = get_num(&v1)?;
    let n0 = NUM::new(&i0.to_string());
    let n1 = NUM::new(&i1.to_string());

    let (d2, n) = derive_times(&n0, &n1)?;

    let rule = Rule::ETimes(d0, d1, d2);
    let v = Value::Value0(Box::new(n));

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(Exp::Exp1(Box::new(Fxp::Fxp2(Box::new(Gxp::Gxp4(
                    Box::new(h.clone()),
                )))))),
                Box::new(EVALTO::new("evalto")),
                Box::new(v.clone()),
            ),
            Box::new(rule),
        ),
        v,
    ))
}

fn eval_ixp(env: &Env, i: &Ixp) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match i {
        Ixp::Ixp0(i0, j1) => {
            let (d0, v0) = eval_ixp(env, i0)?;
            let (d1, v1) = eval_jxp(env, j1)?;

            match &v0 {
                Value::Value2(_, env2, _, _, _, x, _, e0, _) => {
                    let env_ = push_env(env2, x, &v1);

                    let (d2, v2) = eval_exp(&env_, &e0)?;

                    (Rule::EApp(d0, d1, d2), v2)
                }

                Value::Value3(_, env2, _, _, _, x, _, _, y, _, e0, _) => {
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
            }
        }
        Ixp::Ixp1(j) => {
            return eval_jxp(env, j);
        }
    };

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(Exp::Exp1(Box::new(Fxp::Fxp2(Box::new(Gxp::Gxp4(
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
    match j {
        Jxp::Jxp0(n) => eval_num(env, n),
        Jxp::Jxp1(t) => eval_truth(env, t),
        Jxp::Jxp2(x) => eval_env(env, x),
        Jxp::Jxp3(_, e, _) => eval_exp(env, e),
    }
}

fn eval_envlist(el: &EnvList, x: &VAR) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match el {
        EnvList::EnvList0(el_, _, y, _, v) => {
            if x == y.deref() {
                (Rule::EVar1, v.deref().clone())
            } else {
                let (d_, v_) = eval_envlist(el_, x)?;
                (Rule::EVar2(d_), v_)
            }
        }

        EnvList::EnvList1(y, _, v) => {
            if x == y.deref() {
                (Rule::EVar1, v.deref().clone())
            } else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ));
            }
        }
    };

    let j = Judgement::Judgement0(
        Box::new(Env::Env0(Box::new(el.clone()))),
        Box::new(VDASH::new("|-")),
        Box::new(Exp::Exp1(Box::new(Fxp::Fxp2(Box::new(Gxp::Gxp4(
            Box::new(Hxp::Hxp2(Box::new(Ixp::Ixp1(Box::new(Jxp::Jxp2(
                Box::new(x.clone()),
            )))))),
        )))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_env(env: &Env, x: &VAR) -> io::Result<(Derivation, Value)> {
    match env {
        Env::Env0(el) => eval_envlist(el, x),

        Env::Env1() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        )),
    }
}

fn eval_num(env: &Env, n: &NUM) -> io::Result<(Derivation, Value)> {
    let v = Value::Value0(Box::new(n.clone()));

    let j = Judgement::Judgement0(
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(Exp::Exp1(Box::new(Fxp::Fxp2(Box::new(Gxp::Gxp4(
            Box::new(Hxp::Hxp2(Box::new(Ixp::Ixp1(Box::new(Jxp::Jxp0(
                Box::new(n.clone()),
            )))))),
        )))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
    );

    Ok((Derivation(j, Box::new(Rule::EInt)), v))
}

fn eval_truth(env: &Env, t: &TRUTH) -> io::Result<(Derivation, Value)> {
    let v = Value::Value1(Box::new(t.clone()));

    let j = Judgement::Judgement0(
        Box::new(env.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(Exp::Exp1(Box::new(Fxp::Fxp2(Box::new(Gxp::Gxp4(
            Box::new(Hxp::Hxp2(Box::new(Ixp::Ixp1(Box::new(Jxp::Jxp1(
                Box::new(t.clone()),
            )))))),
        )))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(v.clone()),
    );

    Ok((Derivation(j, Box::new(Rule::EBool)), v))
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
