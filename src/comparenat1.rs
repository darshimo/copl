mod rule;

use std::{io, ops::Deref};

use self::rule::{Is, Judgement, Less, Nat, Parser, Than};

#[derive(Debug)]
struct Derivation(Judgement, Box<Rule>);
impl std::fmt::Display for Derivation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} by {}", self.0, self.1)
    }
}

#[derive(Debug)]
enum Rule {
    LSucc,
    LTrans(Derivation, Derivation),
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::LSucc => write!(f, "L-Succ {{}}"),
            Rule::LTrans(d0, d1) => write!(f, "L-Trans {{{};{}}}", d0, d1),
        }
    }
}

fn derive_lessthan(n0: &Nat, n1: &Nat) -> io::Result<Derivation> {
    let rule = match n1.deref() {
        Nat::Nat0(_, _, n1_, _) => {
            if n0 == n1_.deref() {
                Rule::LSucc
            } else {
                let d0_ = derive_lessthan(n0, n1_)?;
                let d1_ = derive_lessthan(n1_, n1)?;

                Rule::LTrans(d0_, d1_)
            }
        }
        Nat::Nat1(_) => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("DerivationError!"),
            ));
        }
    };

    let j = Judgement::Judgement0(
        Box::new(n0.clone()),
        Box::new(Is::new("is")),
        Box::new(Less::new("less")),
        Box::new(Than::new("than")),
        Box::new(n1.clone()),
    );

    Ok(Derivation(j, Box::new(rule)))
}

fn derive(j: &Judgement) -> io::Result<Derivation> {
    let Judgement::Judgement0(n0, _, _, _, n1) = j;

    derive_lessthan(n0, n1)
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
