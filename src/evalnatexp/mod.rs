mod rules;

use regex::Regex;
use rules::{
    Exp,
    Exp::{Exp0, Exp1, ExpDummy2},
    Fxp,
    Fxp::{Fxp0, Fxp1, FxpDummy2},
    Gxp,
    Gxp::{Gxp0, Gxp1},
    Judgement,
    Judgement::{Eval, Plus, Times},
    Nat,
    Nat::{Succ, Zero},
};
use ruly::Parse;

use Rule::*;
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            EConst => write!(f, "E-Const {}{}", r"{", r"}"),
            EPlus(d1, d2, d3) => write!(f, "E-Plus {} {}; {}; {}; {}", r"{", d1, d2, d3, r"}"),
            ETimes(d1, d2, d3) => write!(f, "E-Times {} {}; {}; {}; {}", r"{", d1, d2, d3, r"}"),
            PZero => write!(f, "P-Zero {}{}", r"{", r"}"),
            PSucc(d1) => write!(f, "P-Succ {} {}; {}", r"{", d1, r"}"),
            TZero => write!(f, "T-Zero {}{}", r"{", r"}"),
            TSucc(d1, d2) => write!(f, "T-Succ {} {}; {}; {}", r"{", d1, d2, r"}"),
        }
    }
}

struct Derivation(Judgement, Box<Rule>);
impl std::fmt::Display for Derivation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{} by {}", self.0, self.1)
    }
}

fn derive_bplus(n1: &Nat, n2: &Nat) -> (Nat, Derivation) {
    match n1 {
        Zero(_) => (
            n2.clone(),
            Derivation(
                Times(
                    Box::new(n1.clone()),
                    String::from("plus"),
                    Box::new(n2.clone()),
                    String::from("is"),
                    Box::new(n2.clone()),
                ),
                Box::new(PZero),
            ),
        ),

        Succ(_, _, n, _) => {
            let (ans_, d1) = derive_bplus(n, n2);

            let ans = Succ(
                String::from("S"),
                String::from("("),
                Box::new(ans_),
                String::from(")"),
            );

            (
                ans.clone(),
                Derivation(
                    Times(
                        Box::new(n1.clone()),
                        String::from("plus"),
                        Box::new(n2.clone()),
                        String::from("is"),
                        Box::new(ans),
                    ),
                    Box::new(PSucc(d1)),
                ),
            )
        }
    }
}

fn derive_btimes(n1: &Nat, n2: &Nat) -> (Nat, Derivation) {
    match n1 {
        Zero(_) => (
            n1.clone(),
            Derivation(
                Times(
                    Box::new(n1.clone()),
                    String::from("times"),
                    Box::new(n2.clone()),
                    String::from("is"),
                    Box::new(n1.clone()),
                ),
                Box::new(TZero),
            ),
        ),

        Succ(_, _, n, _) => {
            let (ans1, d1) = derive_btimes(n, n2);
            let (ans, d2) = derive_bplus(n2, &ans1);

            (
                ans.clone(),
                Derivation(
                    Times(
                        Box::new(n1.clone()),
                        String::from("times"),
                        Box::new(n2.clone()),
                        String::from("is"),
                        Box::new(ans),
                    ),
                    Box::new(TSucc(d1, d2)),
                ),
            )
        }
    }
}

fn derive_econst(n: &Nat, e: &Exp) -> (Nat, Derivation) {
    let ans = n.clone();

    (
        ans.clone(),
        Derivation(
            Eval(Box::new(e.clone()), String::from("evalto"), Box::new(ans)),
            Box::new(EConst),
        ),
    )
}

fn derive_eplus(e1: &Exp, f2: &Fxp, e: &Exp) -> (Nat, Derivation) {
    let (ans1, d1) = derive_eval(e1);
    let (ans2, d2) = derive_eval(&Exp1(Box::new(f2.clone())));
    let (ans, d3) = derive_bplus(&ans1, &ans2);

    (
        ans.clone(),
        Derivation(
            Eval(Box::new(e.clone()), String::from("evalto"), Box::new(ans)),
            Box::new(EPlus(d1, d2, d3)),
        ),
    )
}

fn derive_etimes(f1: &Fxp, g2: &Gxp, e: &Exp) -> (Nat, Derivation) {
    let (ans1, d1) = derive_eval(&Exp1(Box::new(f1.clone())));
    let (ans2, d2) = derive_eval(&Exp1(Box::new(Fxp1(Box::new(g2.clone())))));
    let (ans, d3) = derive_btimes(&ans1, &ans2);

    (
        ans.clone(),
        Derivation(
            Eval(Box::new(e.clone()), String::from("evalto"), Box::new(ans)),
            Box::new(ETimes(d1, d2, d3)),
        ),
    )
}

fn derive_eval(e: &Exp) -> (Nat, Derivation) {
    match e {
        ExpDummy2(e1, _, f2) => derive_eplus(e1, f2, e),

        Exp1(f) => match f as &Fxp {
            FxpDummy2(f1, _, g2) => derive_etimes(f1, g2, e),

            Fxp1(g) => match g as &Gxp {
                Gxp0(_, e1, _) => derive_eval(e1),

                Gxp1(n) => derive_econst(n, e),
            },

            _ => panic!(),
        },

        _ => panic!(),
    }
}

fn derive(j: &Judgement) -> Derivation {
    match j {
        Eval(e, _, v) => {
            let e = fix_exp(e);
            let (ans, d) = derive_eval(&e);

            if &ans == v as &Nat {
                return d;
            }
        }

        Plus(n1, _, n2, _, n3) => {
            let (ans, d) = derive_bplus(n1, n2);

            if &ans == n3 as &Nat {
                return d;
            }
        }

        Times(n1, _, n2, _, n3) => {
            let (ans, d) = derive_btimes(n1, n2);

            if &ans == n3 as &Nat {
                return d;
            }
        }
    }

    panic!("Invalid judgement!");
}

fn fix_exp(e: &Exp) -> Exp {
    match e {
        Exp0(f1, s2, e3) => {
            let mut ret = Exp1(Box::new(fix_fxp(f1)));

            let mut op = s2;

            let mut tmp = e3;

            loop {
                if let Exp0(f21, s21, e22) = tmp as &Exp {
                    ret = ExpDummy2(Box::new(ret), op.clone(), Box::new(fix_fxp(f21)));

                    op = s21;

                    tmp = e22;
                } else if let Exp1(f21) = tmp as &Exp {
                    ret = ExpDummy2(Box::new(ret), op.clone(), Box::new(fix_fxp(f21)));
                    break;
                } else {
                    panic!("");
                }
            }

            ret
        }

        Exp1(f) => Exp1(Box::new(fix_fxp(f))),

        _ => panic!("Invalid!"),
    }
}

fn fix_fxp(f: &Fxp) -> Fxp {
    match f {
        Fxp0(g1, s2, f3) => {
            let mut ret = Fxp1(Box::new(fix_gxp(g1)));

            let mut op = s2;

            let mut tmp = f3;

            loop {
                if let Fxp0(g21, s21, f22) = tmp as &Fxp {
                    ret = FxpDummy2(Box::new(ret), op.clone(), Box::new(fix_gxp(g21)));

                    op = s21;

                    tmp = f22;
                } else if let Fxp1(g21) = tmp as &Fxp {
                    ret = FxpDummy2(Box::new(ret), op.clone(), Box::new(fix_gxp(g21)));
                    break;
                } else {
                    panic!("");
                }
            }

            ret
        }

        Fxp1(g) => Fxp1(Box::new(fix_gxp(g))),

        _ => panic!("Invalid!"),
    }
}

fn fix_gxp(g: &Gxp) -> Gxp {
    match g {
        Gxp0(s1, e2, s3) => Gxp0(s1.clone(), Box::new(fix_exp(e2)), s3.clone()),

        _ => g.clone(),
    }
}

pub fn f(s: &str) {
    let mut ruly = ruly::Ruly::new();
    ruly.set_skip_reg(Regex::new(r"[ \n\r\t]*").unwrap());
    ruly.set_input(&s);

    match ruly.run::<Judgement>() {
        Ok(judgement) => {
            println!("{}", judgement);

            println!("{}", derive(&judgement));
        }

        err => {
            println!("{:?}", err);
        }
    }
}
