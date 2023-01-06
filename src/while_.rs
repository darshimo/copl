mod rule;

use std::{io, ops::Deref};

use crate::while_::rule::{COMMA, EQ};

use self::rule::{
    AExp, AFxp, AGxp, BExp, BFxp, BGxp, BHxp, Com, Comp, Coms, Inner, Judgement, Parser, Store,
    CHANGES, EVALTO, NUM, TO, TRUTH, VAR, VDASH,
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
    AConst,
    AVar,
    APlus(Derivation, Derivation),
    AMinus(Derivation, Derivation),
    ATimes(Derivation, Derivation),
    BConst,
    BNot(Derivation),
    BAnd(Derivation, Derivation),
    BOr(Derivation, Derivation),
    BLt(Derivation, Derivation),
    BEq(Derivation, Derivation),
    BLe(Derivation, Derivation),
    CSkip,
    CAssign(Derivation),
    CSeq(Derivation, Derivation),
    CIfT(Derivation, Derivation),
    CIfF(Derivation, Derivation),
    CWhileT(Derivation, Derivation, Derivation),
    CWhileF(Derivation),
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::AConst => write!(f, "A-Const {{}}"),
            Rule::AVar => write!(f, "A-Var {{}}"),
            Rule::APlus(d0, d1) => write!(f, "A-Plus {{{};{}}}", d0, d1),
            Rule::AMinus(d0, d1) => write!(f, "A-Minus {{{};{}}}", d0, d1),
            Rule::ATimes(d0, d1) => write!(f, "A-Times {{{};{}}}", d0, d1),
            Rule::BConst => write!(f, "B-Const {{}}"),
            Rule::BNot(d0) => write!(f, "B-Not {{{}}}", d0),
            Rule::BAnd(d0, d1) => write!(f, "B-And {{{};{}}}", d0, d1),
            Rule::BOr(d0, d1) => write!(f, "B-Or {{{};{}}}", d0, d1),
            Rule::BLt(d0, d1) => write!(f, "B-Lt {{{};{}}}", d0, d1),
            Rule::BEq(d0, d1) => write!(f, "B-Eq {{{};{}}}", d0, d1),
            Rule::BLe(d0, d1) => write!(f, "B-Le {{{};{}}}", d0, d1),
            Rule::CSkip => write!(f, "C-Skip {{}}"),
            Rule::CAssign(d0) => write!(f, "C-Assign {{{}}}", d0),
            Rule::CSeq(d0, d1) => write!(f, "C-Seq {{{};{}}}", d0, d1),
            Rule::CIfT(d0, d1) => write!(f, "C-IfT {{{};{}}}", d0, d1),
            Rule::CIfF(d0, d1) => write!(f, "C-IfF {{{};{}}}", d0, d1),
            Rule::CWhileT(d0, d1, d2) => write!(f, "C-WhileT {{{};{};{}}}", d0, d1, d2),
            Rule::CWhileF(d0) => write!(f, "C-WhileF {{{}}}", d0),
        }
    }
}

fn af2ae(af: AFxp) -> AExp {
    AExp::AExp2(Box::new(af))
}

fn ag2af(ag: AGxp) -> AFxp {
    AFxp::AFxp1(Box::new(ag))
}

fn bf2be(bf: BFxp) -> BExp {
    BExp::BExp1(Box::new(bf))
}

fn bg2bf(bg: BGxp) -> BFxp {
    BFxp::BFxp1(Box::new(bg))
}

fn bh2bg(bh: BHxp) -> BGxp {
    BGxp::BGxp1(Box::new(bh))
}

fn get_num(n: &NUM) -> i32 {
    n.as_str().parse().unwrap()
}

fn get_truth(t: &TRUTH) -> bool {
    t.as_str().parse().unwrap()
}

fn get_var(store: &Store, x: &VAR) -> io::Result<NUM> {
    match store {
        Store::Store0(inner) => match inner.deref() {
            Inner::Inner0(inner_, _, y, _, n) => {
                if x == y.deref() {
                    Ok(n.deref().clone())
                } else {
                    get_var(&Store::Store0(inner_.clone()), x)
                }
            }

            Inner::Inner1(y, _, n) => {
                if x == y.deref() {
                    Ok(n.deref().clone())
                } else {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!4"),
                    ))
                }
            }
        },

        Store::Store1() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!4"),
        )),
    }
}

fn subst_store(store: &Store, x: &VAR, n: &NUM) -> Store {
    match store {
        Store::Store0(inner) => {
            fn f(inner: &Inner, x: &VAR, n: &NUM) -> Inner {
                match inner {
                    Inner::Inner0(inner_, _, y, _, n_) => {
                        let tmp = f(inner_, x, n);

                        if x == y.deref() {
                            Inner::Inner0(
                                Box::new(tmp),
                                Box::new(COMMA::new(",")),
                                y.clone(),
                                Box::new(EQ::new("=")),
                                Box::new(n.clone()),
                            )
                        } else {
                            Inner::Inner0(
                                Box::new(tmp),
                                Box::new(COMMA::new(",")),
                                y.clone(),
                                Box::new(EQ::new("=")),
                                n_.clone(),
                            )
                        }
                    }

                    Inner::Inner1(y, _, n_) => {
                        if x == y.deref() {
                            Inner::Inner1(y.clone(), Box::new(EQ::new("=")), Box::new(n.clone()))
                        } else {
                            Inner::Inner1(y.clone(), Box::new(EQ::new("=")), n_.clone())
                        }
                    }
                }
            }

            Store::Store0(Box::new(f(inner, x, n)))
        }

        Store::Store1() => Store::Store1(),
    }
}

fn eval_aexp(store: &Store, ae: &AExp) -> io::Result<(Derivation, NUM)> {
    let (rule, n) = match ae {
        AExp::AExp0(ae, _ /* + */, af) => {
            let (d0, n0) = eval_aexp(store, ae)?;
            let (d1, n1) = eval_afxp(store, af)?;

            let i0 = get_num(&n0);
            let i1 = get_num(&n1);

            let i2 = i0 + i1;
            let n2 = NUM::new(&i2.to_string());

            (Rule::APlus(d0, d1), n2)
        }

        AExp::AExp1(ae, _ /* - */, af) => {
            let (d0, n0) = eval_aexp(store, ae)?;
            let (d1, n1) = eval_afxp(store, af)?;

            let i0 = get_num(&n0);
            let i1 = get_num(&n1);

            let i2 = i0 - i1;
            let n2 = NUM::new(&i2.to_string());

            (Rule::AMinus(d0, d1), n2)
        }

        AExp::AExp2(af) => {
            return eval_afxp(store, af);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(store.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(ae.clone()),
        Box::new(EVALTO::new("evalto")),
        Box::new(n.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), n))
}

fn eval_afxp(store: &Store, af: &AFxp) -> io::Result<(Derivation, NUM)> {
    let (rule, n) = match af {
        AFxp::AFxp0(af, _ /* * */, ag) => {
            let (d0, n0) = eval_afxp(store, af)?;
            let (d1, n1) = eval_agxp(store, ag)?;

            let i0 = get_num(&n0);
            let i1 = get_num(&n1);

            let i2 = i0 * i1;
            let n2 = NUM::new(&i2.to_string());

            (Rule::ATimes(d0, d1), n2)
        }

        AFxp::AFxp1(ag) => {
            return eval_agxp(store, ag);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(store.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(af2ae(af.clone())),
        Box::new(EVALTO::new("evalto")),
        Box::new(n.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), n))
}

fn eval_agxp(store: &Store, ag: &AGxp) -> io::Result<(Derivation, NUM)> {
    let (rule, n) = match ag {
        AGxp::AGxp0(n) => (Rule::AConst, n.deref().clone()),

        AGxp::AGxp1(x) => {
            let n = get_var(store, x)?;

            (Rule::AVar, n)
        }

        AGxp::AGxp2(_, ae, _) => {
            return eval_aexp(store, ae);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(store.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(af2ae(ag2af(ag.clone()))),
        Box::new(EVALTO::new("evalto")),
        Box::new(n.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), n))
}

fn eval_bexp(store: &Store, be: &BExp) -> io::Result<(Derivation, TRUTH)> {
    let (rule, t) = match be {
        BExp::BExp0(be, _ /* || */, bf) => {
            let (d0, t0) = eval_bexp(store, be)?;
            let (d1, t1) = eval_bfxp(store, bf)?;

            let b0 = get_truth(&t0);
            let b1 = get_truth(&t1);

            let b2 = b0 || b1;
            let t2 = TRUTH::new(&b2.to_string());

            (Rule::BOr(d0, d1), t2)
        }

        BExp::BExp1(bf) => {
            return eval_bfxp(store, bf);
        }
    };

    let j = Judgement::Judgement1(
        Box::new(store.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(be.clone()),
        Box::new(EVALTO::new("evalto")),
        Box::new(t.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), t))
}

fn eval_bfxp(store: &Store, bf: &BFxp) -> io::Result<(Derivation, TRUTH)> {
    let (rule, t) = match bf {
        BFxp::BFxp0(bf, _ /* && */, bg) => {
            let (d0, t0) = eval_bfxp(store, bf)?;
            let (d1, t1) = eval_bgxp(store, bg)?;

            let b0 = get_truth(&t0);
            let b1 = get_truth(&t1);

            let b2 = b0 && b1;
            let t2 = TRUTH::new(&b2.to_string());

            (Rule::BAnd(d0, d1), t2)
        }

        BFxp::BFxp1(bg) => {
            return eval_bgxp(store, bg);
        }
    };

    let j = Judgement::Judgement1(
        Box::new(store.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(bf2be(bf.clone())),
        Box::new(EVALTO::new("evalto")),
        Box::new(t.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), t))
}

fn eval_bgxp(store: &Store, bg: &BGxp) -> io::Result<(Derivation, TRUTH)> {
    let (rule, t) = match bg {
        BGxp::BGxp0(ae0, comp, ae1) => {
            let (d0, n0) = eval_aexp(store, ae0)?;
            let (d1, n1) = eval_aexp(store, ae1)?;

            let i0 = get_num(&n0);
            let i1 = get_num(&n1);

            let (rule, b2) = match comp.deref() {
                Comp::Comp0(_ /* < */) => (Rule::BLt(d0, d1), i0 < i1),
                Comp::Comp1(_ /* = */) => (Rule::BEq(d0, d1), i0 == i1),
                Comp::Comp2(_ /* <= */) => (Rule::BLe(d0, d1), i0 <= i1),
            };
            let t2 = TRUTH::new(&b2.to_string());

            (rule, t2)
        }

        BGxp::BGxp1(bh) => {
            return eval_bhxp(store, bh);
        }
    };

    let j = Judgement::Judgement1(
        Box::new(store.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(bf2be(bg2bf(bg.clone()))),
        Box::new(EVALTO::new("evalto")),
        Box::new(t.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), t))
}

fn eval_bhxp(store: &Store, bh: &BHxp) -> io::Result<(Derivation, TRUTH)> {
    let (rule, t) = match bh {
        BHxp::BHxp0(_ /* ! */, bh) => {
            let (d0, t0) = eval_bhxp(store, bh)?;

            let b0 = get_truth(&t0);

            let b1 = !b0;
            let t1 = TRUTH::new(&b1.to_string());

            (Rule::BNot(d0), t1)
        }

        BHxp::BHxp1(t) => (Rule::BConst, t.deref().clone()),

        BHxp::BHxp2(_, be, _) => {
            return eval_bexp(store, be);
        }
    };

    let j = Judgement::Judgement1(
        Box::new(store.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(bf2be(bg2bf(bh2bg(bh.clone())))),
        Box::new(EVALTO::new("evalto")),
        Box::new(t.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), t))
}

fn eval_coms(coms: &Coms, store: &Store) -> io::Result<(Derivation, Store)> {
    let (rule, store_) = match coms {
        Coms::Coms0(com, _, coms_) => {
            let (d0, store0) = eval_com(com, store)?;
            let (d1, store1) = eval_coms(coms_, &store0)?;

            (Rule::CSeq(d0, d1), store1)
        }

        Coms::Coms1(com) => {
            return eval_com(com, store);
        }
    };

    let j = Judgement::Judgement2(
        Box::new(coms.clone()),
        Box::new(CHANGES::new("changes")),
        Box::new(store.clone()),
        Box::new(TO::new("to")),
        Box::new(store_.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), store_))
}

fn eval_com(com: &Com, store: &Store) -> io::Result<(Derivation, Store)> {
    let (rule, store_) = match com {
        Com::Com0(_ /* skip */) => (Rule::CSkip, store.clone()),

        Com::Com1(x, _ /* assign */, ae) => {
            let (d0, n0) = eval_aexp(store, ae)?;

            let store = subst_store(store, x, &n0);

            (Rule::CAssign(d0), store)
        }

        Com::Com2(_ /* if */, be, _, coms0, _, coms1) => {
            let (d0, t0) = eval_bexp(store, be)?;

            if get_truth(&t0) {
                let (d1, store_) = eval_coms(coms0, store)?;

                (Rule::CIfT(d0, d1), store_)
            } else {
                let (d1, store_) = eval_coms(coms1, store)?;

                (Rule::CIfF(d0, d1), store_)
            }
        }

        Com::Com3(_ /* while */, _, be, _, _, coms) => {
            let (d0, t0) = eval_bexp(store, be)?;

            if get_truth(&t0) {
                let store0 = store;
                let (d1, store1) = eval_coms(coms, store0)?;
                let (d2, store2) = eval_com(com, &store1)?;

                (Rule::CWhileT(d0, d1, d2), store2)
            } else {
                (Rule::CWhileF(d0), store.clone())
            }
        }

        Com::Com4(_, coms, _) => {
            return eval_coms(coms, store);
        }
    };

    let j = Judgement::Judgement2(
        Box::new(Coms::Coms1(Box::new(com.clone()))),
        Box::new(CHANGES::new("changes")),
        Box::new(store.clone()),
        Box::new(TO::new("to")),
        Box::new(store_.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), store_))
}

fn derive(j: &Judgement) -> io::Result<Derivation> {
    match &j {
        Judgement::Judgement0(str, _, ae, _, n) => {
            let (d, n_) = eval_aexp(str, ae)?;
            if n.deref() == &n_ {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!4"),
                ))
            }
        }

        Judgement::Judgement1(str, _, be, _, t) => {
            let (d, t_) = eval_bexp(str, be)?;
            if t.deref() == &t_ {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!4"),
                ))
            }
        }

        Judgement::Judgement2(coms, _, store0, _, store1) => {
            let (d, store_) = eval_coms(coms, store0)?;

            if &store_ == store1.deref() {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!4"),
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
