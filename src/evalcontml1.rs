mod rule;

use std::{io, ops::Deref};

use self::rule::{
    Cont, ContElem, Exp, FinalContElem, Fxp, Gxp, Hxp, Ixp, Judgement, LongExp, Op, Parser, Value,
    AST, CROSS, ELSE, EPASS, EVALTO, HYPHEN, IF, IS, LBRACE, LESS, LT, MINUS, NUM, PLUS, RBRACE,
    THAN, THEN, TIMES, TRUTH, UNDERLINE, VPASS,
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
    EBinOp(Derivation),
    EIf(Derivation),
    CRet,
    CEvalR(Derivation),
    CPlus(Derivation, Derivation),
    CMinus(Derivation, Derivation),
    CTimes(Derivation, Derivation),
    CLt(Derivation, Derivation),
    CIfT(Derivation),
    CIfF(Derivation),
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
            Rule::EBinOp(d0) => write!(f, "E-BinOp {{{}}}", d0),
            Rule::EIf(d0) => write!(f, "E-If {{{}}}", d0),
            Rule::CRet => write!(f, "C-Ret {{}}"),
            Rule::CEvalR(d0) => write!(f, "C-EvalR {{{}}}", d0),
            Rule::CPlus(d0, d1) => write!(f, "C-Plus {{{};{}}}", d0, d1),
            Rule::CMinus(d0, d1) => write!(f, "C-Minus {{{};{}}}", d0, d1),
            Rule::CTimes(d0, d1) => write!(f, "C-Times {{{};{}}}", d0, d1),
            Rule::CLt(d0, d1) => write!(f, "C-Lt {{{};{}}}", d0, d1),
            Rule::CIfT(d0) => write!(f, "C-IfT {{{}}}", d0),
            Rule::CIfF(d0) => write!(f, "C-IfF {{{}}}", d0),
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
    Gxp::Gxp2(Box::new(h))
}

fn i2h(i: Ixp) -> Hxp {
    Hxp::Hxp1(Box::new(i))
}

fn eval_epass_exp(e: &Exp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match e {
        Exp::Exp0(le) => {
            return eval_epass_longexp(le, k_op);
        }

        Exp::Exp1(f) => {
            return eval_epass_fxp(f, k_op);
        }

        Exp::Exp2(g0, _ /* < */, le1) => {
            let e0 = f2e(g2f(g0.deref().clone()));
            let e1 = le2e(le1.deref().clone());

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
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
                None => Cont::Cont1(Box::new(rule::FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(&e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Exp::Exp3(g0, _ /* + */, le1) => {
            let e0 = f2e(g2f(g0.deref().clone()));
            let e1 = le2e(le1.deref().clone());

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
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
                None => Cont::Cont1(Box::new(rule::FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(&e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Exp::Exp4(g0, _ /* - */, le1) => {
            let e0 = f2e(g2f(g0.deref().clone()));
            let e1 = le2e(le1.deref().clone());

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
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
                None => Cont::Cont1(Box::new(rule::FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(&e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Exp::Exp5(h0, _ /* * */, le1) => {
            let e0 = f2e(g2f(h2g(h0.deref().clone())));
            let e1 = le2e(le1.deref().clone());

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
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
                None => Cont::Cont1(Box::new(rule::FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(&e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(e.clone()),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(e.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_longexp(le: &LongExp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match le {
        LongExp::LongExp0(_, e0, _, e1, _, e2) => {
            let ke = ContElem::ContElem2(
                Box::new(LBRACE::new("{")),
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
                None => Cont::Cont1(Box::new(rule::FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(e0, Some(&k_))?;

            (Rule::EIf(d0), v0)
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(le2e(le.clone())),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(le2e(le.clone())),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_fxp(f: &Fxp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match f {
        Fxp::Fxp0(g0, _ /* < */, g1) => {
            let e0 = f2e(g2f(g0.deref().clone()));
            let e1 = f2e(g2f(g1.deref().clone()));

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
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
                None => Cont::Cont1(Box::new(rule::FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(&e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Fxp::Fxp1(g0) => {
            return eval_epass_gxp(g0, k_op);
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(f2e(f.clone())),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(f2e(f.clone())),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_gxp(g: &Gxp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match g {
        Gxp::Gxp0(g0, _ /* + */, h1) => {
            let e0 = f2e(g2f(g0.deref().clone()));
            let e1 = f2e(g2f(h2g(h1.deref().clone())));

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
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
                None => Cont::Cont1(Box::new(rule::FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(&e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Gxp::Gxp1(g0, _ /* - */, h1) => {
            let e0 = f2e(g2f(g0.deref().clone()));
            let e1 = f2e(g2f(h2g(h1.deref().clone())));

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
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
                None => Cont::Cont1(Box::new(rule::FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(&e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Gxp::Gxp2(h0) => {
            return eval_epass_hxp(h0, k_op);
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(f2e(g2f(g.clone()))),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(f2e(g2f(g.clone()))),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_hxp(h: &Hxp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match h {
        Hxp::Hxp0(h0, _ /* * */, i1) => {
            let e0 = f2e(g2f(h2g(h0.deref().clone())));
            let e1 = f2e(g2f(h2g(i2h(i1.deref().clone()))));

            let ke = ContElem::ContElem0(
                Box::new(LBRACE::new("{")),
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
                None => Cont::Cont1(Box::new(rule::FinalContElem::FinalContElem1(Box::new(ke)))),
            };

            let (d0, v0) = eval_epass_exp(&e0, Some(&k_))?;

            (Rule::EBinOp(d0), v0)
        }

        Hxp::Hxp1(i0) => {
            return eval_epass_ixp(i0, k_op);
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(f2e(g2f(h2g(h.clone())))),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(f2e(g2f(h2g(h.clone())))),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),
    };

    Ok((Derivation(j, Box::new(rule)), v))
}

fn eval_epass_ixp(i: &Ixp, k_op: Option<&Cont>) -> io::Result<(Derivation, Value)> {
    let (rule, v) = match i {
        Ixp::Ixp0(n) => {
            let tmp = Cont::Cont1(Box::new(FinalContElem::FinalContElem0(Box::new(
                UNDERLINE::new("_"),
            ))));
            let k = match k_op {
                Some(k) => k,
                None => &tmp,
            };

            let (d0, v0) = eval_vpass(&Value::Value0(n.clone()), k)?;

            (Rule::EInt(d0), v0)
        }

        Ixp::Ixp1(t) => {
            let tmp = Cont::Cont1(Box::new(FinalContElem::FinalContElem0(Box::new(
                UNDERLINE::new("_"),
            ))));
            let k = match k_op {
                Some(k) => k,
                None => &tmp,
            };

            let (d0, v0) = eval_vpass(&Value::Value1(t.clone()), k)?;

            (Rule::EBool(d0), v0)
        }

        Ixp::Ixp2(_, e, _) => {
            return eval_epass_exp(e, k_op);
        }
    };

    let j = match k_op {
        Some(k) => Judgement::Judgement1(
            Box::new(f2e(g2f(h2g(i2h(i.clone()))))),
            Box::new(EPASS::new(">>")),
            Box::new(k.clone()),
            Box::new(EVALTO::new("evalto")),
            Box::new(v.clone()),
        ),

        None => Judgement::Judgement2(
            Box::new(f2e(g2f(h2g(i2h(i.clone()))))),
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

        Some(ContElem::ContElem0(_, _, op, e, _)) => {
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

            let (d0, v1) = eval_epass_exp(e, Some(&k_))?;

            (Rule::CEvalR(d0), v1)
        }

        Some(ContElem::ContElem1(_, v0, op, _, _)) => match (v0.deref(), v) {
            (Value::Value0(n0), Value::Value0(n1)) => {
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
                        let (d1, v1) = eval_vpass(&Value::Value1(Box::new(t)), k_)?;

                        (Rule::CLt(d0, d1), v1)
                    }
                    Op::Op1(_ /* + */) => {
                        let (d0, n) = derive_plus(n0, n1)?;
                        let (d1, v1) = eval_vpass(&Value::Value0(Box::new(n)), k_)?;

                        (Rule::CPlus(d0, d1), v1)
                    }
                    Op::Op2(_ /* - */) => {
                        let (d0, n) = derive_minus(n0, n1)?;
                        let (d1, v1) = eval_vpass(&Value::Value0(Box::new(n)), k_)?;

                        (Rule::CMinus(d0, d1), v1)
                    }
                    Op::Op3(_ /* * */) => {
                        let (d0, n) = derive_times(n0, n1)?;
                        let (d1, v1) = eval_vpass(&Value::Value0(Box::new(n)), k_)?;

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
        },

        Some(ContElem::ContElem2(_, _, _, _, e1, _, e2, _)) => match v {
            Value::Value1(t) => {
                if t.as_str() == "true" {
                    let (d0, v0) = eval_epass_exp(e1, k_op)?;
                    (Rule::CIfT(d0), v0)
                } else {
                    let (d0, v0) = eval_epass_exp(e2, k_op)?;
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
        Judgement::Judgement0(v0, _, k, _, v1) => {
            let (d, v_) = eval_vpass(v0, k)?;

            if &v_ == v1.deref() {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement1(e, _, k, _, v) => {
            let (d, v_) = eval_epass_exp(e, Some(k))?;

            if &v_ == v.deref() {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement2(e, _, v) => {
            let (d, v_) = eval_epass_exp(e, None)?;

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
