mod rule;

use std::{io, ops::Deref};

use self::rule::{
    Arrow, ArrowM, Exp, Fxp, Gxp, Is, Judgement, Lparen, Nat, Parser, Plus, Rparen, Succ, Times,
    Zero, M, P,
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
    RPlus(Derivation),
    RTimes(Derivation),
    RPlusL(Derivation),
    RPlusR(Derivation),
    RTimesL(Derivation),
    RTimesR(Derivation),

    DRPlus(Derivation),
    DRTimes(Derivation),
    DRPlusL(Derivation),
    DRPlusR(Derivation),
    DRTimesL(Derivation),
    DRTimesR(Derivation),

    MRZero,
    MRMulti(Derivation, Derivation),
    MROne(Derivation),

    PZero,
    PSucc(Derivation),
    TZero,
    TSucc(Derivation, Derivation),
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::RPlus(d0) => write!(f, "R-Plus {{{}}}", d0),
            Rule::RTimes(d0) => write!(f, "R-Times {{{}}}", d0),
            Rule::RPlusL(d0) => write!(f, "R-PlusL {{{}}}", d0),
            Rule::RPlusR(d0) => write!(f, "R-PlusR {{{}}}", d0),
            Rule::RTimesL(d0) => write!(f, "R-TimesL {{{}}}", d0),
            Rule::RTimesR(d0) => write!(f, "R-TimesR {{{}}}", d0),

            Rule::DRPlus(d0) => write!(f, "DR-Plus {{{}}}", d0),
            Rule::DRTimes(d0) => write!(f, "DR-Times {{{}}}", d0),
            Rule::DRPlusL(d0) => write!(f, "DR-PlusL {{{}}}", d0),
            Rule::DRPlusR(d0) => write!(f, "DR-PlusR {{{}}}", d0),
            Rule::DRTimesL(d0) => write!(f, "DR-TimesL {{{}}}", d0),
            Rule::DRTimesR(d0) => write!(f, "DR-TimesR {{{}}}", d0),

            Rule::MRZero => write!(f, "MR-Zero {{}}"),
            Rule::MRMulti(d0, d1) => write!(f, "MR-Multi {{{};{}}}", d0, d1),
            Rule::MROne(d0) => write!(f, "MR-One {{{}}}", d0),

            Rule::PZero => write!(f, "P-Zero {{}}"),
            Rule::PSucc(d0) => write!(f, "P-Succ {{{}}}", d0),
            Rule::TZero => write!(f, "T-Zero {{}}"),
            Rule::TSucc(d0, d1) => write!(f, "T-Succ {{{};{}}}", d0, d1),
        }
    }
}

fn normalize_exp(e: &Exp) -> (bool, Exp) {
    match e {
        Exp::Exp0(e0, _, f0) => {
            let (e0_is_normalized, e0_) = normalize_exp(e0);
            let (f0_is_normalized, f0_) = normalize_fxp(f0);

            (
                e0_is_normalized || f0_is_normalized,
                Exp::Exp0(Box::new(e0_), Box::new(P::new("+")), Box::new(f0_)),
            )
        }

        Exp::Exp1(f) => {
            let (f_is_normalized, f_) = normalize_fxp(f);

            if let Fxp::Fxp1(g_) = &f_ {
                if let Gxp::Gxp0(_, e_, _) = g_.deref() {
                    return (true, e_.deref().clone());
                }
            }

            (f_is_normalized, f2e(&f_))
        }
    }
}

fn normalize_fxp(f: &Fxp) -> (bool, Fxp) {
    match f {
        Fxp::Fxp0(f0, _, g0) => {
            let (f0_is_normalized, f0_) = normalize_fxp(f0);
            let (g0_is_normalized, g0_) = normalize_gxp(g0);

            (
                f0_is_normalized || g0_is_normalized,
                Fxp::Fxp0(Box::new(f0_), Box::new(M::new("*")), Box::new(g0_)),
            )
        }

        Fxp::Fxp1(g) => {
            let (g_is_normalized, g_) = normalize_gxp(g);

            if let Gxp::Gxp0(_, e_, _) = &g_ {
                if let Exp::Exp1(f_) = e_.deref() {
                    return (true, f_.deref().clone());
                }
            }

            (g_is_normalized, g2f(&g_))
        }
    }
}

fn normalize_gxp(g: &Gxp) -> (bool, Gxp) {
    match g {
        Gxp::Gxp0(_, e, _) => {
            let (is_normalized, e_) = normalize_exp(e);

            if let Exp::Exp1(f_) = &e_ {
                if let Fxp::Fxp1(g_) = f_.deref() {
                    return (true, g_.deref().clone());
                }
            }

            (
                is_normalized,
                Gxp::Gxp0(
                    Box::new(Lparen::new("(")),
                    Box::new(e_),
                    Box::new(Rparen::new(")")),
                ),
            )
        }

        Gxp::Gxp1(_) => (false, g.clone()),
    }
}

fn get_nat_from_exp(e: &Exp) -> Option<Nat> {
    if let Exp::Exp1(f) = e {
        if let Fxp::Fxp1(g) = f.deref() {
            if let Gxp::Gxp1(n) = g.deref() {
                return Some(n.deref().clone());
            }
        }
    }

    None
}

fn get_nat_from_fxp(f: &Fxp) -> Option<Nat> {
    if let Fxp::Fxp1(g) = f.deref() {
        if let Gxp::Gxp1(n) = g.deref() {
            return Some(n.deref().clone());
        }
    }

    None
}

fn get_nat_from_gxp(g: &Gxp) -> Option<Nat> {
    if let Gxp::Gxp1(n) = g.deref() {
        return Some(n.deref().clone());
    }

    None
}

fn derive_reduce(e0: &Exp, e1: &Exp) -> io::Result<Derivation> {
    let j = Judgement::Judgement0(
        Box::new(e0.clone()),
        Box::new(Arrow::new("--->")),
        Box::new(e1.clone()),
    );

    match (e0, e1) {
        (Exp::Exp0(e0_, _, f0_), Exp::Exp0(e1_, _, f1_)) => {
            if e0_ != e1_ && f0_ == f1_ {
                let d0 = derive_reduce(e0_, e1_)?;

                return Ok(Derivation(j, Box::new(Rule::RPlusL(d0))));
            } else if e0_ == e1_ && f0_ != f1_ {
                let d0 = derive_reduce(&normalize_exp(&f2e(f0_)).1, &normalize_exp(&f2e(f1_)).1)?;

                return Ok(Derivation(j, Box::new(Rule::RPlusR(d0))));
            }
        }

        (Exp::Exp1(f0_), Exp::Exp1(f1_)) => match (f0_.deref(), f1_.deref()) {
            (Fxp::Fxp0(f0__, _, g0__), Fxp::Fxp0(f1__, _, g1__)) => {
                if f0__ != f1__ && g0__ == g1__ {
                    let d0 =
                        derive_reduce(&normalize_exp(&f2e(f0__)).1, &normalize_exp(&f2e(f1__)).1)?;

                    return Ok(Derivation(j, Box::new(Rule::RTimesL(d0))));
                } else if f0__ == f1__ && g0__ != g1__ {
                    let d0 =
                        derive_reduce(&normalize_exp(&g2e(g0__)).1, &normalize_exp(&g2e(g1__)).1)?;

                    return Ok(Derivation(j, Box::new(Rule::RTimesR(d0))));
                }
            }

            (Fxp::Fxp0(f0__, _, g1__), Fxp::Fxp1(g2__)) => {
                if let (Some(n0), Some(n1), Some(n2)) = (
                    get_nat_from_fxp(f0__),
                    get_nat_from_gxp(g1__),
                    get_nat_from_gxp(g2__),
                ) {
                    let (d0, n2_) = derive_times(&n0, &n1)?;

                    if n2 == n2_ {
                        return Ok(Derivation(j, Box::new(Rule::RTimes(d0))));
                    }
                }
            }

            _ => {}
        },

        (Exp::Exp0(e0_, _, f1_), Exp::Exp1(f2_)) => {
            if let (Some(n0), Some(n1), Some(n2)) = (
                get_nat_from_exp(e0_),
                get_nat_from_fxp(f1_),
                get_nat_from_fxp(f2_),
            ) {
                let (d0, n2_) = derive_plus(&n0, &n1)?;

                if n2 == n2_ {
                    return Ok(Derivation(j, Box::new(Rule::RPlus(d0))));
                }
            }
        }

        _ => {}
    }

    Err(io::Error::new(
        io::ErrorKind::InvalidInput,
        format!("DerivationError!"),
    ))
}

fn derive_reduce_d(e0: &Exp, e1: &Exp) -> io::Result<Derivation> {
    let j = Judgement::Judgement0(
        Box::new(e0.clone()),
        Box::new(Arrow::new("-d->")),
        Box::new(e1.clone()),
    );

    match (e0, e1) {
        (Exp::Exp0(e0_, _, f0_), Exp::Exp0(e1_, _, f1_)) => {
            if e0_ != e1_ && f0_ == f1_ {
                let d0 = derive_reduce_d(e0_, e1_)?;

                return Ok(Derivation(j, Box::new(Rule::DRPlusL(d0))));
            } else if e0_ == e1_ && f0_ != f1_ && get_nat_from_exp(e0_) != None {
                let d0 = derive_reduce_d(&normalize_exp(&f2e(f0_)).1, &normalize_exp(&f2e(f1_)).1)?;

                return Ok(Derivation(j, Box::new(Rule::DRPlusR(d0))));
            }
        }

        (Exp::Exp1(f0_), Exp::Exp1(f1_)) => match (f0_.deref(), f1_.deref()) {
            (Fxp::Fxp0(f0__, _, g0__), Fxp::Fxp0(f1__, _, g1__)) => {
                if f0__ != f1__ && g0__ == g1__ {
                    let d0 = derive_reduce_d(
                        &normalize_exp(&Exp::Exp1(f0__.clone())).1,
                        &normalize_exp(&Exp::Exp1(f1__.clone())).1,
                    )?;

                    return Ok(Derivation(j, Box::new(Rule::DRTimesL(d0))));
                } else if f0__ == f1__ && g0__ != g1__ && get_nat_from_fxp(f0__) != None {
                    let d0 = derive_reduce_d(
                        &normalize_exp(&g2e(g0__)).1,
                        &normalize_exp(&g2e(g1__)).1,
                    )?;

                    return Ok(Derivation(j, Box::new(Rule::DRTimesR(d0))));
                }
            }

            (Fxp::Fxp0(f0__, _, g1__), Fxp::Fxp1(g2__)) => {
                if let (Some(n0), Some(n1), Some(n2)) = (
                    get_nat_from_fxp(f0__),
                    get_nat_from_gxp(g1__),
                    get_nat_from_gxp(g2__),
                ) {
                    let (d0, n2_) = derive_times(&n0, &n1)?;

                    if n2 == n2_ {
                        return Ok(Derivation(j, Box::new(Rule::DRTimes(d0))));
                    }
                }
            }

            _ => {}
        },

        (Exp::Exp0(e0_, _, f1_), Exp::Exp1(f2_)) => {
            if let (Some(n0), Some(n1), Some(n2)) = (
                get_nat_from_exp(e0_),
                get_nat_from_fxp(f1_),
                get_nat_from_fxp(f2_),
            ) {
                let (d0, n2_) = derive_plus(&n0, &n1)?;

                if n2 == n2_ {
                    return Ok(Derivation(j, Box::new(Rule::DRPlus(d0))));
                }
            }
        }

        _ => {}
    }

    Err(io::Error::new(
        io::ErrorKind::InvalidInput,
        format!("DerivationError!"),
    ))
}

fn f2e(f: &Fxp) -> Exp {
    Exp::Exp1(Box::new(f.clone()))
}

fn g2f(g: &Gxp) -> Fxp {
    Fxp::Fxp1(Box::new(g.clone()))
}

fn e2g(e: &Exp) -> Gxp {
    Gxp::Gxp0(
        Box::new(Lparen::new("(")),
        Box::new(e.clone()),
        Box::new(Rparen::new(")")),
    )
}

fn g2e(g: &Gxp) -> Exp {
    f2e(&g2f(g))
}

fn e2f(e: &Exp) -> Fxp {
    g2f(&e2g(e))
}

fn onestep_any(e: &Exp) -> Option<Exp> {
    match e {
        Exp::Exp0(e_, _, f_) => {
            if let Some(e__) = onestep_any(e_) {
                Some(Exp::Exp0(
                    Box::new(e__),
                    Box::new(P::new("+")),
                    Box::new(f_.deref().clone()),
                ))
            } else if let Some(tmp) = onestep_any(&normalize_exp(&f2e(f_)).1) {
                let f__ = normalize_fxp(&e2f(&tmp)).1;
                Some(Exp::Exp0(
                    Box::new(e_.deref().clone()),
                    Box::new(P::new("+")),
                    Box::new(f__),
                ))
            } else if let (Some(n0), Some(n1)) = (get_nat_from_exp(e_), get_nat_from_fxp(f_)) {
                Some(g2e(&Gxp::Gxp1(Box::new(add_of_nat(&n0, &n1)))))
            } else {
                None
            }
        }

        Exp::Exp1(f) => match f.deref() {
            Fxp::Fxp0(f_, _, g_) => {
                if let Some(tmp) = onestep_any(&normalize_exp(&f2e(f_)).1) {
                    let f__ = normalize_fxp(&e2f(&tmp)).1;
                    Some(f2e(&Fxp::Fxp0(
                        Box::new(f__),
                        Box::new(M::new("*")),
                        Box::new(g_.deref().clone()),
                    )))
                } else if let Some(tmp) = onestep_any(&normalize_exp(&g2e(g_)).1) {
                    let g__ = normalize_gxp(&e2g(&tmp)).1;
                    Some(f2e(&Fxp::Fxp0(
                        Box::new(f_.deref().clone()),
                        Box::new(M::new("*")),
                        Box::new(g__),
                    )))
                } else if let (Some(n0), Some(n1)) = (get_nat_from_fxp(f_), get_nat_from_gxp(g_)) {
                    Some(g2e(&Gxp::Gxp1(Box::new(mul_of_nat(&n0, &n1)))))
                } else {
                    None
                }
            }

            Fxp::Fxp1(g) => match g.deref() {
                Gxp::Gxp0(_, e_, _) => onestep_any(e_),

                Gxp::Gxp1(_) => None,
            },
        },
    }
}

fn nat2int(n: &Nat) -> u32 {
    if let Nat::Nat0(_, _, n_, _) = n {
        1 + nat2int(n_)
    } else {
        0
    }
}

fn int2nat(i: u32) -> Nat {
    if i > 0 {
        Nat::Nat0(
            Box::new(Succ::new("S")),
            Box::new(Lparen::new("(")),
            Box::new(int2nat(i - 1)),
            Box::new(Rparen::new(")")),
        )
    } else {
        Nat::Nat1(Box::new(Zero::new("Z")))
    }
}

fn add_of_nat(n0: &Nat, n1: &Nat) -> Nat {
    int2nat(nat2int(n0) + nat2int(n1))
}

fn mul_of_nat(n0: &Nat, n1: &Nat) -> Nat {
    int2nat(nat2int(n0) * nat2int(n1))
}

fn onestep(e0: &Exp, e1: &Exp) -> io::Result<Exp> {
    match (e0, e1) {
        (Exp::Exp0(e0_, _, f0_), Exp::Exp0(e1_, _, f1_)) => {
            if e0_ != e1_ {
                let e = onestep(e0_, e1_)?;
                return Ok(Exp::Exp0(
                    Box::new(e),
                    Box::new(P::new("+")),
                    Box::new(f0_.deref().clone()),
                ));
            } else if f0_ != f1_ {
                let f = normalize_fxp(&g2f(&Gxp::Gxp0(
                    Box::new(Lparen::new("(")),
                    Box::new(onestep(
                        &normalize_exp(&f2e(f0_)).1,
                        &normalize_exp(&f2e(f1_)).1,
                    )?),
                    Box::new(Rparen::new(")")),
                )))
                .1;

                return Ok(Exp::Exp0(
                    Box::new(e0_.deref().clone()),
                    Box::new(P::new("+")),
                    Box::new(f),
                ));
            }
        }

        (Exp::Exp1(f0_), Exp::Exp1(f1_)) => match (f0_.deref(), f1_.deref()) {
            (Fxp::Fxp0(f0__, _, g0__), Fxp::Fxp0(f1__, _, g1__)) => {
                if f0__ != f1__ {
                    let f = normalize_fxp(&g2f(&Gxp::Gxp0(
                        Box::new(Lparen::new("(")),
                        Box::new(onestep(
                            &normalize_exp(&f2e(f0__)).1,
                            &normalize_exp(&f2e(f1__)).1,
                        )?),
                        Box::new(Rparen::new(")")),
                    )))
                    .1;

                    return Ok(f2e(&Fxp::Fxp0(
                        Box::new(f),
                        Box::new(M::new("*")),
                        Box::new(g0__.deref().clone()),
                    )));
                } else if g0__ != g1__ {
                    let g = normalize_gxp(&Gxp::Gxp0(
                        Box::new(Lparen::new("(")),
                        Box::new(onestep(
                            &normalize_exp(&g2e(g0__)).1,
                            &normalize_exp(&g2e(g1__)).1,
                        )?),
                        Box::new(Rparen::new(")")),
                    ))
                    .1;

                    return Ok(f2e(&Fxp::Fxp0(
                        Box::new(f0__.deref().clone()),
                        Box::new(M::new("*")),
                        Box::new(g),
                    )));
                }
            }

            (Fxp::Fxp0(f0__, _, g1__), Fxp::Fxp1(g2__)) => {
                if let Some(n2) = get_nat_from_gxp(g2__) {
                    if let Some(tmp) = onestep_any(&normalize_exp(&f2e(f0__)).1) {
                        let f = normalize_fxp(&g2f(&Gxp::Gxp0(
                            Box::new(Lparen::new("(")),
                            Box::new(tmp),
                            Box::new(Rparen::new(")")),
                        )))
                        .1;

                        return Ok(f2e(&Fxp::Fxp0(
                            Box::new(f),
                            Box::new(M::new("*")),
                            Box::new(g1__.deref().clone()),
                        )));
                    } else if let Some(tmp) = onestep_any(&normalize_exp(&g2e(g1__)).1) {
                        let g = normalize_gxp(&Gxp::Gxp0(
                            Box::new(Lparen::new("(")),
                            Box::new(tmp),
                            Box::new(Rparen::new(")")),
                        ))
                        .1;

                        return Ok(f2e(&Fxp::Fxp0(
                            Box::new(f0__.deref().clone()),
                            Box::new(M::new("*")),
                            Box::new(g),
                        )));
                    } else if let (Some(n0), Some(n1)) =
                        (get_nat_from_fxp(f0__), get_nat_from_gxp(g1__))
                    {
                        if nat2int(&n0) * nat2int(&n1) == nat2int(&n2) {
                            return Ok(e1.clone());
                        }
                    }
                }
            }

            _ => {}
        },

        (Exp::Exp0(e0_, _, f1_), Exp::Exp1(f2_)) => {
            if let Some(n2) = get_nat_from_fxp(f2_) {
                if let Some(e) = onestep_any(e0_) {
                    return Ok(Exp::Exp0(
                        Box::new(e),
                        Box::new(P::new("+")),
                        Box::new(f1_.deref().clone()),
                    ));
                } else if let Some(tmp) = onestep_any(&normalize_exp(&f2e(f1_)).1) {
                    let f = normalize_fxp(&g2f(&Gxp::Gxp0(
                        Box::new(Lparen::new("(")),
                        Box::new(tmp),
                        Box::new(Rparen::new(")")),
                    )))
                    .1;

                    return Ok(Exp::Exp0(
                        Box::new(e0_.deref().clone()),
                        Box::new(P::new("+")),
                        Box::new(f),
                    ));
                } else if let (Some(n0), Some(n1)) = (get_nat_from_exp(e0_), get_nat_from_fxp(f1_))
                {
                    if nat2int(&n0) + nat2int(&n1) == nat2int(&n2) {
                        return Ok(e1.clone());
                    }
                }
            }
        }

        _ => {}
    }

    Err(io::Error::new(
        io::ErrorKind::InvalidInput,
        format!("DerivationError!"),
    ))
}

fn derive_reduce_m(e0: &Exp, e1: &Exp) -> io::Result<Derivation> {
    let rule = if e0 == e1 {
        Rule::MRZero
    } else {
        let e = onestep(e0, e1)?;
        let d1 = derive_reduce_m(&e, e1)?;
        let d0_ = derive_reduce(e0, &e)?;
        let j0 = Judgement::Judgement2(
            Box::new(e0.clone()),
            Box::new(ArrowM::new("-*->")),
            Box::new(e),
        );
        let d0 = Derivation(j0, Box::new(Rule::MROne(d0_)));
        Rule::MRMulti(d0, d1)
    };
    let j = Judgement::Judgement2(
        Box::new(e0.clone()),
        Box::new(ArrowM::new("-*->")),
        Box::new(e1.clone()),
    );
    Ok(Derivation(j, Box::new(rule)))
}

fn derive_plus(n0: &Nat, n1: &Nat) -> io::Result<(Derivation, Nat)> {
    let (n2, rule) = match n0 {
        Nat::Nat0(_, _, n0_, _) => {
            let (d0_, n2_) = derive_plus(n0_, n1)?;

            let n2 = Nat::Nat0(
                Box::new(Succ::new("S")),
                Box::new(Lparen::new("(")),
                Box::new(n2_),
                Box::new(Rparen::new(")")),
            );

            (n2, Rule::PSucc(d0_))
        }
        Nat::Nat1(_) => {
            let n2 = n1.clone();

            (n2, Rule::PZero)
        }
    };

    let j = Judgement::Judgement3(
        Box::new(n0.clone()),
        Box::new(Plus::new("plus")),
        Box::new(n1.clone()),
        Box::new(Is::new("is")),
        Box::new(n2.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), n2))
}

fn derive_times(n0: &Nat, n1: &Nat) -> io::Result<(Derivation, Nat)> {
    let (n2, rule) = match n0 {
        Nat::Nat0(_, _, n0_, _) => {
            let (d0_, n3) = derive_times(n0_, n1)?;
            let (d1_, n2) = derive_plus(n1, &n3)?;

            (n2, Rule::TSucc(d0_, d1_))
        }
        Nat::Nat1(_) => {
            let n2 = Nat::Nat1(Box::new(Zero::new("Z")));

            (n2, Rule::TZero)
        }
    };

    let j = Judgement::Judgement4(
        Box::new(n0.clone()),
        Box::new(Times::new("times")),
        Box::new(n1.clone()),
        Box::new(Is::new("is")),
        Box::new(n2.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), n2))
}

fn derive(j: &Judgement) -> io::Result<Derivation> {
    match j {
        Judgement::Judgement0(e0, _, e1) => {
            derive_reduce(&normalize_exp(e0).1, &normalize_exp(e1).1)
        }

        Judgement::Judgement1(e0, _, e1) => {
            derive_reduce_d(&normalize_exp(e0).1, &normalize_exp(e1).1)
        }

        Judgement::Judgement2(e0, _, e1) => {
            derive_reduce_m(&normalize_exp(e0).1, &normalize_exp(e1).1)
        }

        Judgement::Judgement3(n0, _, n1, _, n2) => {
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

        Judgement::Judgement4(n0, _, n1, _, n2) => {
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
