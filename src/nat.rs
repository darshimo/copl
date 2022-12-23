mod rule;

use std::{io, ops::Deref};

use self::rule::{Is, Judgement, Lparen, Nat, Parser, Plus, Rparen, Succ, Times, Zero};

#[derive(Debug)]
struct Derivation(Judgement, Box<Rule>);
impl std::fmt::Display for Derivation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} by {}", self.0, self.1)
    }
}

#[derive(Debug)]
enum Rule {
    PZero,
    PSucc(Derivation),
    TZero,
    TSucc(Derivation, Derivation),
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::PZero => write!(f, "P-Zero {{}}"),
            Rule::PSucc(d0) => write!(f, "P-Succ {{{}}}", d0),
            Rule::TZero => write!(f, "T-Zero {{}}"),
            Rule::TSucc(d0, d1) => write!(f, "T-Succ {{{};{}}}", d0, d1),
        }
    }
}

fn derive_plus(n0: &Nat, n1: &Nat) -> io::Result<(Derivation, Nat)> {
    let (n2, rule) = match n0.deref() {
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

    let j = Judgement::Judgement0(
        Box::new(n0.clone()),
        Box::new(Plus::new("plus")),
        Box::new(n1.clone()),
        Box::new(Is::new("is")),
        Box::new(n2.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), n2))
}

fn derive_times(n0: &Nat, n1: &Nat) -> io::Result<(Derivation, Nat)> {
    let (n2, rule) = match n0.deref() {
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

    let j = Judgement::Judgement1(
        Box::new(n0.clone()),
        Box::new(Times::new("times")),
        Box::new(n1.clone()),
        Box::new(Is::new("is")),
        Box::new(n2.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), n2))
}

fn derive(j: &Judgement) -> io::Result<Derivation> {
    match &j {
        Judgement::Judgement0(n0, _, n1, _, n2) => {
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
        Judgement::Judgement1(n0, _, n1, _, n2) => {
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
