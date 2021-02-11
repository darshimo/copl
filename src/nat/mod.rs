pub mod rules;

use regex::Regex;
use rules::{
    Judgement,
    Judgement::{Plus, Times},
    Nat,
    Nat::{Succ, Zero},
};
use ruly::Parse;

enum Rule {
    PZero(),
    PSucc(Derivation),
    TZero(),
    TSucc(Derivation, Derivation),
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            PZero() => write!(f, "P-Zero {}{}", r"{", r"}"),
            PSucc(d1) => write!(f, "P-Succ {} {}; {}", r"{", d1, r"}"),
            TZero() => write!(f, "T-Zero {}{}", r"{", r"}"),
            TSucc(d1, d2) => write!(f, "T-Succ {} {}; {}; {}", r"{", d1, d2, r"}"),
        }
    }
}

use Rule::*;

struct Derivation(Judgement, Box<Rule>);
impl std::fmt::Display for Derivation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{} by {}", self.0, self.1)
    }
}

fn derive_plus(n1: &Nat, n2: &Nat) -> (Nat, Derivation) {
    match n1 {
        Zero(_) => (
            n2.clone(),
            Derivation(
                Plus(
                    Box::new(n1.clone()),
                    String::from("plus"),
                    Box::new(n2.clone()),
                    String::from("is"),
                    Box::new(n2.clone()),
                ),
                Box::new(PZero()),
            ),
        ),

        Succ(_, _, n1_, _) => {
            let (ans_, d_) = derive_plus(n1_, n2);

            let ans = Succ(
                String::from("S"),
                String::from("("),
                Box::new(ans_),
                String::from(")"),
            );

            let d = Derivation(
                Plus(
                    Box::new(n1.clone()),
                    String::from("plus"),
                    Box::new(n2.clone()),
                    String::from("is"),
                    Box::new(ans.clone()),
                ),
                Box::new(PSucc(d_)),
            );

            (ans, d)
        }
    }
}

fn derive_times(n1: &Nat, n2: &Nat) -> (Nat, Derivation) {
    match n1 {
        Zero(_) => (
            n1.clone(),
            Derivation(
                Plus(
                    Box::new(n1.clone()),
                    String::from("times"),
                    Box::new(n2.clone()),
                    String::from("is"),
                    Box::new(n1.clone()),
                ),
                Box::new(TZero()),
            ),
        ),

        Succ(_, _, n1_, _) => {
            let (ans1_, d1_) = derive_times(n1_, n2);
            let (ans2_, d2_) = derive_plus(n2, &ans1_);

            (
                ans2_.clone(),
                Derivation(
                    Plus(
                        Box::new(n1.clone()),
                        String::from("times"),
                        Box::new(n2.clone()),
                        String::from("is"),
                        Box::new(ans2_),
                    ),
                    Box::new(TSucc(d1_, d2_)),
                ),
            )
        }
    }
}

fn derive(j: &Judgement) -> Derivation {
    match j {
        Plus(n1, _, n2, _, n3) => {
            let (ans, d) = derive_plus(&n1, &n2);
            if n3 as &Nat == &ans {
                return d;
            }
        }

        Times(n1, _, n2, _, n3) => {
            let (ans, d) = derive_times(&n1, &n2);
            if n3 as &Nat == &ans {
                return d;
            } else {
            }
        }
    }

    panic!("Invalid judgement!");
}

pub fn f(s: &str) {
    let mut ruly = ruly::Ruly::new();
    ruly.set_skip_reg(Regex::new(r"[ \n\r\t]*").unwrap());
    ruly.set_input(&s);

    match ruly.run::<Judgement>() {
        Ok(judgement) => {
            println!("{}", derive(&judgement));
        }

        err => {
            println!("{:?}", err);
        }
    }
}
