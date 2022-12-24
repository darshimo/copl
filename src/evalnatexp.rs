mod rule;

use std::{io, ops::Deref};

use self::rule::{
    Evalto, Exp, Fxp, Gxp, Is, Judgement, Lparen, Nat, Parser, Plus, Rparen, Succ, Times, Zero,
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
    EConst,
    EPlus(Derivation, Derivation, Derivation),
    ETimes(Derivation, Derivation, Derivation),
    PZero,
    PSucc(Derivation),
    TZero,
    TSucc(Derivation, Derivation),
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::EConst => write!(f, "E-Const {{}}"),
            Rule::EPlus(d0, d1, d2) => write!(f, "E-Plus {{{};{};{}}}", d0, d1, d2),
            Rule::ETimes(d0, d1, d2) => write!(f, "E-Times {{{};{};{}}}", d0, d1, d2),
            Rule::PZero => write!(f, "P-Zero {{}}"),
            Rule::PSucc(d0) => write!(f, "P-Succ {{{}}}", d0),
            Rule::TZero => write!(f, "T-Zero {{}}"),
            Rule::TSucc(d0, d1) => write!(f, "T-Succ {{{};{}}}", d0, d1),
        }
    }
}

fn derive_exp(e: &Exp) -> io::Result<(Derivation, Nat)> {
    match e {
        Exp::Exp0(e0, _ /* "+" */, f0) => {
            let (d0, n0) = derive_exp(e0)?;
            let (d1, n1) = derive_fxp(f0)?;
            let (d2, n2) = derive_plus(&n0, &n1)?;

            let j = Judgement::Judgement0(
                Box::new(e.clone()),
                Box::new(Evalto::new("evalto")),
                Box::new(n2.clone()),
            );

            let rule = Rule::EPlus(d0, d1, d2);

            let d = Derivation(j, Box::new(rule));

            Ok((d, n2))
        }

        Exp::Exp1(f0) => derive_fxp(f0),
    }
}

fn derive_fxp(f: &Fxp) -> io::Result<(Derivation, Nat)> {
    match f {
        Fxp::Fxp0(f0, _ /* "*" */, g0) => {
            let (d0_, n0_) = derive_fxp(f0)?;
            let (d1_, n1_) = derive_gxp(g0)?;
            let (d2_, n2) = derive_times(&n0_, &n1_)?;

            let j = Judgement::Judgement0(
                Box::new(Exp::Exp1(Box::new(f.clone()))),
                Box::new(Evalto::new("evalto")),
                Box::new(n2.clone()),
            );

            let rule = Rule::ETimes(d0_, d1_, d2_);

            let d = Derivation(j, Box::new(rule));

            Ok((d, n2))
        }

        Fxp::Fxp1(g0) => derive_gxp(g0),
    }
}

fn derive_gxp(g: &Gxp) -> io::Result<(Derivation, Nat)> {
    match g {
        Gxp::Gxp0(_, e0, _) => derive_exp(e0),
        Gxp::Gxp1(n0) => derive_nat(n0),
    }
}

fn derive_nat(n: &Nat) -> io::Result<(Derivation, Nat)> {
    let rule = Rule::EConst;
    let j = Judgement::Judgement0(
        Box::new(Exp::Exp1(Box::new(Fxp::Fxp1(Box::new(Gxp::Gxp1(
            Box::new(n.clone()),
        )))))),
        Box::new(Evalto::new("evalto")),
        Box::new(n.clone()),
    );
    Ok((Derivation(j, Box::new(rule)), n.clone()))
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

    let j = Judgement::Judgement1(
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

    let j = Judgement::Judgement2(
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
        Judgement::Judgement0(e, _, n) => {
            let (d, n_) = derive_exp(e)?;

            if n.deref() == &n_ {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement1(n0, _, n1, _, n2) => {
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

        Judgement::Judgement2(n0, _, n1, _, n2) => {
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
