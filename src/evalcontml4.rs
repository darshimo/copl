mod rule;

use std::{io, ops::Deref};

use self::rule::{
    Cont, ContElem, Element, Env, EnvList, Exp, FinalContElem, Fxp, Gxp, Hxp, Ixp, Judgement, Jxp,
    Kxp, LongExp, Op, Parser, Value, ARROW, AST, BAR, COMMA, CONS, CROSS, ELSE, EPASS, EQ, EVALTO,
    FUN, HYPHEN, IF, IN, IS, LBRACE, LBRACKET, LESS, LET, LPAREN, LT, MATCH, MINUS, NUM, PLUS,
    RBRACE, RBRACKET, REC, RPAREN, THAN, THEN, TIMES, TRUTH, UNDERLINE, VAR, VDASH, VPASS, WITH,
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
    EInt(Derivation),
    EBool(Derivation),
    EIf(Derivation),
    EBinOp(Derivation),
    EVar(Derivation),
    ELet(Derivation),
    EFun(Derivation),
    EApp(Derivation),
    ELetRec(Derivation),
    ENil(Derivation),
    ECons(Derivation),
    EMatch(Derivation),
    ELetCc(Derivation),
    CRet,
    CEvalR(Derivation),
    CPlus(Derivation, Derivation),
    CMinus(Derivation, Derivation),
    CTimes(Derivation, Derivation),
    CLt(Derivation, Derivation),
    CIfT(Derivation),
    CIfF(Derivation),
    CLetBody(Derivation),
    CEvalArg(Derivation),
    CEvalFun(Derivation),
    CEvalFunR(Derivation),
    CEvalFunC(Derivation),
    CEvalConsR(Derivation),
    CCons(Derivation),
    CMatchNil(Derivation),
    CMatchCons(Derivation),
    BPlus,
    BMinus,
    BTimes,
    BLt,
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::EInt(d0) => write!(f, "E-Int {{{}}}", d0),
            Rule::EBool(d0) => write!(f, "E-Bool {{{}}}", d0),
            Rule::EIf(d0) => write!(f, "E-If {{{}}}", d0),
            Rule::EBinOp(d0) => write!(f, "E-BinOp {{{}}}", d0),
            Rule::EVar(d0) => write!(f, "E-Var {{{}}}", d0),
            Rule::ELet(d0) => write!(f, "E-Let {{{}}}", d0),
            Rule::EFun(d0) => write!(f, "E-Fun {{{}}}", d0),
            Rule::EApp(d0) => write!(f, "E-App {{{}}}", d0),
            Rule::ELetRec(d0) => write!(f, "E-LetRec {{{}}}", d0),
            Rule::ENil(d0) => write!(f, "E-Nil {{{}}}", d0),
            Rule::ECons(d0) => write!(f, "E-Cons {{{}}}", d0),
            Rule::EMatch(d0) => write!(f, "E-Match {{{}}}", d0),
            Rule::ELetCc(d0) => write!(f, "E-LetCc {{{}}}", d0),
            Rule::CRet => write!(f, "C-Ret {{}}"),
            Rule::CEvalR(d0) => write!(f, "C-EvalR {{{}}}", d0),
            Rule::CPlus(d0, d1) => write!(f, "C-Plus {{{};{}}}", d0, d1),
            Rule::CMinus(d0, d1) => write!(f, "C-Minus {{{};{}}}", d0, d1),
            Rule::CTimes(d0, d1) => write!(f, "C-Times {{{};{}}}", d0, d1),
            Rule::CLt(d0, d1) => write!(f, "C-Lt {{{};{}}}", d0, d1),
            Rule::CIfT(d0) => write!(f, "C-IfT {{{}}}", d0),
            Rule::CIfF(d0) => write!(f, "C-IfF {{{}}}", d0),
            Rule::CLetBody(d0) => write!(f, "C-LetBody {{{}}}", d0),
            Rule::CEvalArg(d0) => write!(f, "C-EvalArg {{{}}}", d0),
            Rule::CEvalFun(d0) => write!(f, "C-EvalFun {{{}}}", d0),
            Rule::CEvalFunR(d0) => write!(f, "C-EvalFunR {{{}}}", d0),
            Rule::CEvalFunC(d0) => write!(f, "C-EvalFunC {{{}}}", d0),
            Rule::CEvalConsR(d0) => write!(f, "C-EvalConsR {{{}}}", d0),
            Rule::CCons(d0) => write!(f, "C-Cons {{{}}}", d0),
            Rule::CMatchNil(d0) => write!(f, "C-MatchNil {{{}}}", d0),
            Rule::CMatchCons(d0) => write!(f, "C-MatchCons {{{}}}", d0),
            Rule::BPlus => write!(f, "B-Plus {{}}"),
            Rule::BMinus => write!(f, "B-Minus {{}}"),
            Rule::BTimes => write!(f, "B-Times {{}}"),
            Rule::BLt => write!(f, "B-Lt {{}}"),
        }
    }
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

fn eval_var(env: &Env, x: &VAR) -> io::Result<Value> {
    match env {
        Env::Env0(el) => match el.deref() {
            EnvList::EnvList0(el_, _, y, _, v) => {
                if x == y.deref() {
                    Ok(v.deref().clone())
                } else {
                    eval_var(&Env::Env0(el_.clone()), x)
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

// fn cons(v0: &Value, v1: &Value) -> Value {
//     match v0 {
//         Value::Value0(_, _, _) => Value::Value0(
//             Box::new(Element::Element5(
//                 Box::new(LPAREN::new("(")),
//                 Box::new(v0.clone()),
//                 Box::new(RPAREN::new(")")),
//             )),
//             Box::new(CONS::new("::")),
//             Box::new(v1.clone()),
//         ),
//         Value::Value1(elem) => Value::Value0(
//             elem.clone(),
//             Box::new(CONS::new("::")),
//             Box::new(v1.clone()),
//         ),
//     }
// }

// fn pop(v: &Value) -> io::Result<Option<(Value, Value)>> {
//     match v {
//         Value::Value0(elem, _, v1) => Ok(Some((Value::Value1(elem.clone()), v1.deref().clone()))),
//         Value::Value1(elem) => match elem.deref() {
//             Element::Element4(_, _) => Ok(None),
//             Element::Element5(_, v_, _) => pop(v_),
//             _ => Err(io::Error::new(
//                 io::ErrorKind::InvalidInput,
//                 format!("DerivationError!"),
//             )),
//         },
//     }
// }

fn normalize_value(v: &Value) -> Value {
    match v {
        Value::Value1(elem) => match elem.deref() {
            Element::Element6(_, v_, _) => normalize_value(v_),
            _ => v.clone(),
        },
        _ => v.clone(),
    }
}

fn eval_epass_exp(env: &Env, e: &Exp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match e {
        Exp::Exp0(le) => {
            return eval_epass_longexp(env, le, k_op);
        }

        Exp::Exp1(f) => {
            return eval_epass_fxp(env, f, k_op);
        }

        Exp::Exp2(g0, _ /* < */, le1) => {
            let e0 = f2e(g2f(g0.deref().clone()));
            let e1 = le2e(le1.deref().clone());

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(Op::Op0(Box::new(LT::new("<")))),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Exp::Exp3(h0, _ /* :: */, le1) => {
            let e0 = f2e(g2f(h2g(h0.deref().clone())));
            let e1 = le2e(le1.deref().clone());

            let ke = ContElem::ContElem6(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(CONS::new("::")),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::ECons(d0), v0)
        }

        Exp::Exp4(h0, _ /* + */, le1) => {
            let e0 = f2e(g2f(h2g(h0.deref().clone())));
            let e1 = le2e(le1.deref().clone());

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(Op::Op1(Box::new(CROSS::new("+")))),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Exp::Exp5(h0, _ /* - */, le1) => {
            let e0 = f2e(g2f(h2g(h0.deref().clone())));
            let e1 = le2e(le1.deref().clone());

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(Op::Op2(Box::new(HYPHEN::new("-")))),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Exp::Exp6(i0, _ /* * */, le1) => {
            let e0 = f2e(g2f(h2g(i2h(i0.deref().clone()))));
            let e1 = le2e(le1.deref().clone());

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(Op::Op3(Box::new(AST::new("*")))),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(e.clone()),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(e.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_longexp(
    env: &Env,
    le: &LongExp,
    k_op: Option<&Cont>,
) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match le {
        LongExp::LongExp0(_, e0, _, e1, _, e2) => {
            let ke = ContElem::ContElem2(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(IF::new("if")),
                Box::new(UNDERLINE::new("_")),
                Box::new(THEN::new("then")),
                e1.clone(),
                Box::new(ELSE::new("else")),
                e2.clone(),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, e0, Some(&k_))?;

            (Rule::EIf(d0), v0)
        }

        LongExp::LongExp1(_, x, _, e0, _, e1) => {
            let ke = ContElem::ContElem3(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(LET::new("let")),
                x.clone(),
                Box::new(EQ::new("=")),
                Box::new(UNDERLINE::new("_")),
                Box::new(IN::new("in")),
                e1.clone(),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, e0, Some(&k_))?;

            (Rule::ELet(d0), v0)
        }

        LongExp::LongExp2(_, x, _, e) => {
            let v = Value::Value1(Box::new(Element::Element2(
                Box::new(LPAREN::new("(")),
                Box::new(env.clone()),
                Box::new(RPAREN::new(")")),
                Box::new(LBRACKET::new("[")),
                Box::new(FUN::new("fun")),
                x.clone(),
                Box::new(ARROW::new("->")),
                e.clone(),
                Box::new(RBRACKET::new("]")),
            )));

            let tmp = Cont::Cont1(Box::new(FinalContElem::FinalContElem0(Box::new(
                UNDERLINE::new("_"),
            ))));
            let k_ = match k_op {
                Some(k) => k,
                None => &tmp,
            };

            let (d0, v0) = eval_vpass(&v, &k_)?;

            (Rule::EFun(d0), v0)
        }

        LongExp::LongExp3(_, _, x, _, _, y, _, e0, _, e1) => {
            let v = Value::Value1(Box::new(Element::Element3(
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
            )));

            let env_ = push_env(env, x, &v);

            let (d0, v0) = eval_epass_exp(&env_, e1, k_op)?;

            (Rule::ELetRec(d0), v0)
        }

        LongExp::LongExp4(_, e0, _, _, _, _, e1, _, x, _, y, _, e2) => {
            let ke = ContElem::ContElem8(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(MATCH::new("match")),
                Box::new(UNDERLINE::new("_")),
                Box::new(WITH::new("with")),
                Box::new(LBRACKET::new("[")),
                Box::new(RBRACKET::new("]")),
                Box::new(ARROW::new("->")),
                e1.clone(),
                Box::new(BAR::new("|")),
                x.clone(),
                Box::new(CONS::new("::")),
                y.clone(),
                Box::new(ARROW::new("->")),
                e2.clone(),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, e0, Some(&k_))?;

            (Rule::EMatch(d0), v0)
        }

        LongExp::LongExp5(_, x, _, e) => {
            let tmp = Cont::Cont1(Box::new(FinalContElem::FinalContElem0(Box::new(
                UNDERLINE::new("_"),
            ))));
            let k_ = match k_op {
                Some(k) => k,
                None => &tmp,
            };

            let v = Value::Value1(Box::new(Element::Element5(
                Box::new(LBRACKET::new("[")),
                Box::new(k_.clone()),
                Box::new(RBRACKET::new("]")),
            )));
            let env_ = push_env(env, x, &v);

            let (d0, v0) = eval_epass_exp(&env_, e, k_op)?;

            (Rule::ELetCc(d0), v0)
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(le2e(le.clone())),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(le2e(le.clone())),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_fxp(env: &Env, f: &Fxp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match f {
        Fxp::Fxp0(g0, _ /* < */, g1) => {
            let e0 = f2e(g2f(g0.deref().clone()));
            let e1 = f2e(g2f(g1.deref().clone()));

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(Op::Op0(Box::new(LT::new("<")))),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Fxp::Fxp1(g0) => {
            return eval_epass_gxp(env, g0, k_op);
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(f.clone())),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(f.clone())),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_gxp(env: &Env, g: &Gxp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match g {
        Gxp::Gxp0(h0, _ /* :: */, g1) => {
            let e0 = f2e(g2f(h2g(h0.deref().clone())));
            let e1 = f2e(g2f(g1.deref().clone()));

            let ke = ContElem::ContElem6(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(CONS::new("::")),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::ECons(d0), v0)
        }

        Gxp::Gxp1(h0) => {
            return eval_epass_hxp(env, h0, k_op);
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(g2f(g.clone()))),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(g2f(g.clone()))),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_hxp(env: &Env, h: &Hxp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match h {
        Hxp::Hxp0(h0, _ /* + */, i1) => {
            let e0 = f2e(g2f(h2g(h0.deref().clone())));
            let e1 = f2e(g2f(h2g(i2h(i1.deref().clone()))));

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(Op::Op1(Box::new(CROSS::new("+")))),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Hxp::Hxp1(h0, _ /* - */, i1) => {
            let e0 = f2e(g2f(h2g(h0.deref().clone())));
            let e1 = f2e(g2f(h2g(i2h(i1.deref().clone()))));

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(Op::Op2(Box::new(HYPHEN::new("-")))),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Hxp::Hxp2(i0) => {
            return eval_epass_ixp(env, i0, k_op);
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(g2f(h2g(h.clone())))),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(g2f(h2g(h.clone())))),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_ixp(env: &Env, i: &Ixp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match i {
        Ixp::Ixp0(i0, _ /* * */, j1) => {
            let e0 = f2e(g2f(h2g(i2h(i0.deref().clone()))));
            let e1 = f2e(g2f(h2g(i2h(j2i(j1.deref().clone())))));

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(Op::Op3(Box::new(AST::new("*")))),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Ixp::Ixp1(j0) => {
            return eval_epass_jxp(env, j0, k_op);
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(g2f(h2g(i2h(i.clone()))))),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(g2f(h2g(i2h(i.clone()))))),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_jxp(env: &Env, j: &Jxp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match j {
        Jxp::Jxp0(j0, k1) => {
            let e0 = f2e(g2f(h2g(i2h(j2i(j0.deref().clone())))));
            let e1 = f2e(g2f(h2g(i2h(j2i(k2j(k1.deref().clone()))))));

            let ke = ContElem::ContElem4(
                Box::new(LBRACE::new("{")),
                Box::new(env.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(UNDERLINE::new("_")),
                Box::new(e1),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k) => Cont::Cont0(
                    Box::new(ke),
                    Box::new(EPASS::new(">>")),
                    Box::new(k.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(env, &e0, Some(&k_))?;

            (Rule::EApp(d0), v0)
        }

        Jxp::Jxp1(k0) => {
            return eval_epass_kxp(env, k0, k_op);
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(g2f(h2g(i2h(j2i(j.clone())))))),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(g2f(h2g(i2h(j2i(j.clone())))))),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_kxp(env: &Env, k: &Kxp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let tmp = Cont::Cont1(Box::new(FinalContElem::FinalContElem0(Box::new(
        UNDERLINE::new("_"),
    ))));
    let k_ = match k_op {
        Some(k_) => k_,
        None => &tmp,
    };

    let (rule, v) = match k {
        Kxp::Kxp0(n) => {
            let (d0, v0) = eval_vpass(&Value::Value1(Box::new(Element::Element0(n.clone()))), k_)?;
            (Rule::EInt(d0), v0)
        }

        Kxp::Kxp1(t) => {
            let (d0, v0) = eval_vpass(&Value::Value1(Box::new(Element::Element1(t.clone()))), k_)?;
            (Rule::EBool(d0), v0)
        }

        Kxp::Kxp2(x) => {
            let (d0, v0) = eval_vpass(&eval_var(env, x)?, k_)?;
            (Rule::EVar(d0), v0)
        }

        Kxp::Kxp3(_, _) => {
            let (d0, v0) = eval_vpass(
                &Value::Value1(Box::new(Element::Element4(
                    Box::new(LBRACKET::new("[")),
                    Box::new(RBRACKET::new("]")),
                ))),
                k_,
            )?;

            (Rule::ENil(d0), v0)
        }

        Kxp::Kxp4(_, e, _) => {
            return eval_epass_exp(env, e, k_op);
        }
    };

    let j = match k_op {
        Some(k_) => Judgement::Judgement1(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(g2f(h2g(i2h(j2i(k2j(k.clone()))))))),
            Box::new(EPASS::new(">>")),
            Box::new(k_.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(env.clone()),
            Box::new(VDASH::new("|-")),
            Box::new(f2e(g2f(h2g(i2h(j2i(k2j(k.clone()))))))),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_vpass(v: &Value, k: &Cont) -> io::Result<(Derivation, Value)> {
    let (ke_op, k_op) = match k {
        Cont::Cont0(ke, _, k_) => (Some(ke.deref()), Some(k_.deref())),
        Cont::Cont1(fke) => match fke.deref() {
            FinalContElem::FinalContElem0(_ /* _ */) => (None, None),
            FinalContElem::FinalContElem1(ke) => (Some(ke.deref()), None),
        },
    };

    let (rule, v_) = match ke_op {
        None => (Rule::CRet, v.clone()),

        Some(ContElem::ContElem0(_, env, _, _, op, e, _)) => {
            let ke_ = ContElem::ContElem1(
                Box::new(LBRACE::new("{")),
                Box::new(v.clone()),
                op.clone(),
                Box::new(UNDERLINE::new("_")),
                Box::new(RBRACE::new("}")),
            );

            let k_ = match k_op {
                Some(k_) => Cont::Cont0(
                    Box::new(ke_),
                    Box::new(EPASS::new(">>")),
                    Box::new(k_.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke_)))),
            };

            let (d0, v1) = eval_epass_exp(env, e, Some(&k_))?;

            (Rule::CEvalR(d0), v1)
        }

        Some(ContElem::ContElem1(_, v0, op, _, _)) => match (v0.deref(), v) {
            (Value::Value1(elem0), Value::Value1(elem1)) => {
                match (elem0.deref(), elem1.deref()) {
                    (Element::Element0(n0), Element::Element0(n1)) => {
                        let tmp = Cont::Cont1(Box::new(FinalContElem::FinalContElem0(Box::new(
                            UNDERLINE::new("_"),
                        ))));
                        let k_ = match k_op {
                            Some(k_) => k_,
                            None => &tmp,
                        };

                        match op.deref() {
                            Op::Op0(_ /* < */) => {
                                let (d0, t) = derive_lt(n0, n1)?;
                                let (d1, v1) = eval_vpass(
                                    &Value::Value1(Box::new(Element::Element1(Box::new(t)))),
                                    k_,
                                )?;

                                (Rule::CLt(d0, d1), v1)
                            }
                            Op::Op1(_ /* + */) => {
                                let (d0, n) = derive_plus(n0, n1)?;
                                let (d1, v1) = eval_vpass(
                                    &Value::Value1(Box::new(Element::Element0(Box::new(n)))),
                                    k_,
                                )?;

                                (Rule::CPlus(d0, d1), v1)
                            }
                            Op::Op2(_ /* - */) => {
                                let (d0, n) = derive_minus(n0, n1)?;
                                let (d1, v1) = eval_vpass(
                                    &Value::Value1(Box::new(Element::Element0(Box::new(n)))),
                                    k_,
                                )?;

                                (Rule::CMinus(d0, d1), v1)
                            }
                            Op::Op3(_ /* * */) => {
                                let (d0, n) = derive_times(n0, n1)?;
                                let (d1, v1) = eval_vpass(
                                    &Value::Value1(Box::new(Element::Element0(Box::new(n)))),
                                    k_,
                                )?;

                                (Rule::CTimes(d0, d1), v1)
                            }
                        }
                    }

                    _ => {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            format!("DerivationError!"),
                        ));
                    }
                }
            }

            _ => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ));
            }
        },

        Some(ContElem::ContElem2(_, env, _, _ /* if */, _, _, e1, _, e2, _)) => {
            match normalize_value(v) {
                Value::Value1(elem) => match *elem {
                    Element::Element1(t) => {
                        if t.as_str() == "true" {
                            let (d0, v0) = eval_epass_exp(env, e1, k_op)?;
                            (Rule::CIfT(d0), v0)
                        } else {
                            let (d0, v0) = eval_epass_exp(env, e2, k_op)?;
                            (Rule::CIfF(d0), v0)
                        }
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

        Some(ContElem::ContElem3(_, env, _, _ /* let */, x, _, _, _, e, _)) => {
            let (d0, v0) = eval_epass_exp(&push_env(env, x, v), e, k_op)?;
            (Rule::CLetBody(d0), v0)
        }

        Some(ContElem::ContElem4(_, env, _, _, e, _)) => {
            // app
            let ke_ = ContElem::ContElem5(
                Box::new(LBRACE::new("{")),
                Box::new(v.clone()),
                Box::new(UNDERLINE::new("_")),
                Box::new(RBRACE::new("}")),
            );
            let k_ = match k_op {
                Some(tmp) => Cont::Cont0(
                    Box::new(ke_),
                    Box::new(EPASS::new(">>")),
                    Box::new(tmp.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke_)))),
            };
            let (d0, v0) = eval_epass_exp(env, e, Some(&k_))?;
            (Rule::CEvalArg(d0), v0)
        }

        Some(ContElem::ContElem5(_, v_, _, _)) => {
            // app
            match normalize_value(v_) {
                Value::Value1(elem) => {
                    match *elem {
                        Element::Element2(_, env, _, _, _ /* fun */, x, _, e, _) => {
                            let (d0, v0) = eval_epass_exp(&push_env(&env, &x, v), &e, k_op)?;
                            (Rule::CEvalFun(d0), v0)
                        }

                        Element::Element3(_, env, _, _, _ /* rec */, x, _, _, y, _, e, _) => {
                            let (d0, v0) = eval_epass_exp(
                                &push_env(&push_env(&env, &x, v_), &y, v),
                                &e,
                                k_op,
                            )?;
                            (Rule::CEvalFunR(d0), v0)
                        }

                        Element::Element5(_, k_, _) => {
                            let (d0, v0) = eval_vpass(v, &k_)?;
                            (Rule::CEvalFunC(d0), v0)
                        }

                        _ => {
                            return Err(io::Error::new(
                                io::ErrorKind::InvalidInput,
                                format!("DerivationError!"),
                            ));
                        }
                    }
                }

                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!"),
                    ));
                }
            }
        }

        Some(ContElem::ContElem6(_, env, _, _, _ /* :: */, e, _)) => {
            let el = match v {
                Value::Value0(_, _, _) => Element::Element6(
                    Box::new(LPAREN::new("(")),
                    Box::new(v.clone()),
                    Box::new(RPAREN::new(")")),
                ),
                Value::Value1(el_) => el_.deref().clone(),
            };
            let ke_ = ContElem::ContElem7(
                Box::new(LBRACE::new("{")),
                Box::new(el),
                Box::new(CONS::new("::")),
                Box::new(UNDERLINE::new("_")),
                Box::new(RBRACE::new("}")),
            );
            let k_ = match k_op {
                Some(tmp) => Cont::Cont0(
                    Box::new(ke_),
                    Box::new(EPASS::new(">>")),
                    Box::new(tmp.clone()),
                ),
                None => Cont::Cont1(Box::new(FinalContElem::FinalContElem1(Box::new(ke_)))),
            };
            let (d0, v0) = eval_epass_exp(env, e, Some(&k_))?;
            (Rule::CEvalConsR(d0), v0)
        }

        Some(ContElem::ContElem7(_, el0, _ /* :: */, _, _)) => {
            let v_ = Value::Value0(el0.clone(), Box::new(CONS::new("::")), Box::new(v.clone()));

            let tmp = Cont::Cont1(Box::new(FinalContElem::FinalContElem0(Box::new(
                UNDERLINE::new("_"),
            ))));
            let k_ = match k_op {
                Some(k) => k,
                None => &tmp,
            };

            let (d0, v0) = eval_vpass(&v_, k_)?;
            (Rule::CCons(d0), v0)
        }

        Some(ContElem::ContElem8(
            _,
            env,
            _,
            _, /* match */
            _,
            _,
            _,
            _,
            _,
            e0,
            _,
            x,
            _,
            y,
            _,
            e1,
            _,
        )) => match normalize_value(v) {
            Value::Value0(el, _, v_) => {
                let (d0, v0) = eval_epass_exp(
                    &push_env(
                        &push_env(env, x, &normalize_value(&Value::Value1(el))),
                        y,
                        &v_,
                    ),
                    e1,
                    k_op,
                )?;
                (Rule::CMatchCons(d0), v0)
            }

            Value::Value1(el) => match el.deref() {
                Element::Element4(_, _) => {
                    let (d0, v0) = eval_epass_exp(env, e0, k_op)?;
                    (Rule::CMatchNil(d0), v0)
                }

                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!"),
                    ));
                }
            },
        },
    };

    let j = Judgement::Judgement0(
        Box::new(v.clone()),
        Box::new(VPASS::new("=>")),
        Box::new(k.clone()),
        Box::new(EVALTO::new("evalto")),
        Box::new(v_.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), v_))
}

fn derive_plus(n0: &NUM, n1: &NUM) -> io::Result<(Derivation, NUM)> {
    let i0: i32 = n0.as_str().parse().unwrap();
    let i1: i32 = n1.as_str().parse().unwrap();
    let n2 = NUM::new(&(i0 + i1).to_string());

    let j = Judgement::Judgement3(
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

    let j = Judgement::Judgement4(
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

    let j = Judgement::Judgement5(
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

    let j = Judgement::Judgement6(
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
        Judgement::Judgement0(v0, _, k, _, r) => {
            let (d, r_) = eval_vpass(v0, k)?;
            if r.deref() == &r_ {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement1(env, _, e, _, k, _, v) => {
            let (d, v_) = eval_epass_exp(env, e, Some(k))?;

            if &v_ == v.deref() {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement2(env, _, e, _, v) => {
            let (d, v_) = eval_epass_exp(env, e, None)?;

            if &v_ == v.deref() {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement3(n0, _ /* plus */, n1, _, n2) => {
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

        Judgement::Judgement4(n0, _ /* minus */, n1, _, n2) => {
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

        Judgement::Judgement5(n0, _ /* times */, n1, _, n2) => {
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

        Judgement::Judgement6(n0, _ /* less */, _ /* than */, n1, _, t2) => {
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
