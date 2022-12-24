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
    LZero,
    LSuccSucc(Derivation),
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::LZero => write!(f, "L-Zero {{}}"),
            Rule::LSuccSucc(d0) => write!(f, "L-SuccSucc {{{}}}", d0),
        }
    }
}

fn derive_lessthan(n0: &Nat, n1: &Nat) -> io::Result<Derivation> {
    let rule = match n1.deref() {
        Nat::Nat0(_, _, n1_, _) => match n0.deref() {
            Nat::Nat0(_, _, n0_, _) => {
                let d0_ = derive_lessthan(n0_, n1_)?;
                Rule::LSuccSucc(d0_)
            }

            Nat::Nat1(_) => Rule::LZero,
        },
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
