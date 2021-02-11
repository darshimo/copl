mod rules;

use regex::Regex;
use rules::{
    Bool,
    Bool::Bool0,
    Exp,
    Exp::{Exp0, Exp1},
    Fxp,
    Fxp::{Fxp0, Fxp1, FxpDummy2},
    Gxp,
    Gxp::{Gxp0, Gxp1, GxpDummy2},
    Hxp,
    Hxp::{Hxp0, Hxp1, Hxp2, Hxp3},
    Int,
    Int::Int0,
    Judgement,
    Judgement::{Eval, Lt, Minus, Plus, Times},
    Value,
    Value::{Value0, Value1},
};
use ruly::Parse;

use Rule::*;
enum Rule {
    EInt,
    EBool,
    EIfT(Derivation, Derivation),
    EIfF(Derivation, Derivation),
    EPlus(Derivation, Derivation, Derivation),
    EMinus(Derivation, Derivation, Derivation),
    ETimes(Derivation, Derivation, Derivation),
    ELt(Derivation, Derivation, Derivation),
    BPlus,
    BMinus,
    BTimes,
    BLt,
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            EInt => write!(f, "E-Int {}{}", r"{", r"}"),
            EBool => write!(f, "E-Bool {}{}", r"{", r"}"),
            EIfT(d1, d2) => write!(f, "E-IfT {} {}; {}; {}", r"{", d1, d2, r"}"),
            EIfF(d1, d2) => write!(f, "E-IfF {} {}; {}; {}", r"{", d1, d2, r"}"),
            EPlus(d1, d2, d3) => write!(f, "E-Plus {} {}; {}; {}; {}", r"{", d1, d2, d3, r"}"),
            EMinus(d1, d2, d3) => write!(f, "E-Minus {} {}; {}; {}; {}", r"{", d1, d2, d3, r"}"),
            ETimes(d1, d2, d3) => write!(f, "E-Times {} {}; {}; {}; {}", r"{", d1, d2, d3, r"}"),
            ELt(d1, d2, d3) => write!(f, "E-Lt {} {}; {}; {}; {}", r"{", d1, d2, d3, r"}"),
            BPlus => write!(f, "B-Plus {}{}", r"{", r"}"),
            BMinus => write!(f, "B-Minus {}{}", r"{", r"}"),
            BTimes => write!(f, "B-Times {}{}", r"{", r"}"),
            BLt => write!(f, "B-Lt {}{}", r"{", r"}"),
        }
    }
}

struct Derivation(Judgement, Box<Rule>);
impl std::fmt::Display for Derivation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{} by {}", self.0, self.1)
    }
}

fn derive_bplus(n1: &Int, n2: &Int) -> (Int, Derivation) {
    let Int0((_, i1)) = n1;
    let Int0((_, i2)) = n2;

    let i3 = *i1 + *i2;

    (
        Int0((i3.to_string(), i3)),
        Derivation(
            Plus(
                Box::new(Int0((i1.to_string(), *i1))),
                String::from("plus"),
                Box::new(Int0((i2.to_string(), *i2))),
                String::from("is"),
                Box::new(Int0((i3.to_string(), i3))),
            ),
            Box::new(BPlus),
        ),
    )
}

fn derive_bminus(n1: &Int, n2: &Int) -> (Int, Derivation) {
    let Int0((_, i1)) = n1 as &Int;
    let Int0((_, i2)) = n2 as &Int;

    let i3 = *i1 - *i2;

    (
        Int0((i3.to_string(), i3)),
        Derivation(
            Minus(
                Box::new(Int0((i1.to_string(), *i1))),
                String::from("minus"),
                Box::new(Int0((i2.to_string(), *i2))),
                String::from("is"),
                Box::new(Int0((i3.to_string(), i3))),
            ),
            Box::new(BMinus),
        ),
    )
}

fn derive_btimes(n1: &Int, n2: &Int) -> (Int, Derivation) {
    let Int0((_, i1)) = n1 as &Int;
    let Int0((_, i2)) = n2 as &Int;

    let i3 = *i1 * *i2;

    (
        Int0((i3.to_string(), i3)),
        Derivation(
            Times(
                Box::new(Int0((i1.to_string(), *i1))),
                String::from("times"),
                Box::new(Int0((i2.to_string(), *i2))),
                String::from("is"),
                Box::new(Int0((i3.to_string(), i3))),
            ),
            Box::new(BTimes),
        ),
    )
}

fn derive_blt(n1: &Int, n2: &Int) -> (Bool, Derivation) {
    let Int0((_, i1)) = n1 as &Int;
    let Int0((_, i2)) = n2 as &Int;

    let b3 = *i1 < *i2;

    (
        Bool0((b3.to_string(), b3)),
        Derivation(
            Lt(
                Box::new(Int0((i1.to_string(), *i1))),
                String::from("less"),
                String::from("than"),
                Box::new(Int0((i2.to_string(), *i2))),
                String::from("is"),
                Box::new(Bool0((b3.to_string(), b3))),
            ),
            Box::new(BLt),
        ),
    )
}

fn derive_eint(n: &Int, e: &Exp) -> (Value, Derivation) {
    let ans = Value0(Box::new(n.clone()));

    (
        ans.clone(),
        Derivation(
            Eval(Box::new(e.clone()), String::from("evalto"), Box::new(ans)),
            Box::new(EInt),
        ),
    )
}

fn derive_ebool(m: &Bool, e: &Exp) -> (Value, Derivation) {
    let ans = Value1(Box::new(m.clone()));

    (
        ans.clone(),
        Derivation(
            Eval(Box::new(e.clone()), String::from("evalto"), Box::new(ans)),
            Box::new(EBool),
        ),
    )
}

fn derive_eif(e1: &Exp, e2: &Exp, e3: &Exp, e: &Exp) -> (Value, Derivation) {
    let (ans1, d1) = derive_eval(e1);

    if let Value1(m1) = ans1 {
        let Bool0((_, b1)) = *m1;

        if b1 {
            let (ans, d2) = derive_eval(e2);

            (
                ans.clone(),
                Derivation(
                    Eval(Box::new(e.clone()), String::from("evalto"), Box::new(ans)),
                    Box::new(EIfT(d1, d2)),
                ),
            )
        } else {
            let (ans, d2) = derive_eval(e3);

            (
                ans.clone(),
                Derivation(
                    Eval(Box::new(e.clone()), String::from("evalto"), Box::new(ans)),
                    Box::new(EIfF(d1, d2)),
                ),
            )
        }
    } else {
        panic!()
    }
}

fn derive_eplus(f1: &Fxp, g2: &Gxp, e: &Exp) -> (Value, Derivation) {
    let (ans1, d1) = derive_eval(&Exp1(Box::new(f1.clone())));
    let (ans2, d2) = derive_eval(&Exp1(Box::new(Fxp1(Box::new(g2.clone())))));

    if let (Value0(n1), Value0(n2)) = (ans1, ans2) {
        let (ans, d3) = derive_bplus(&n1, &n2);

        (
            Value0(Box::new(ans.clone())),
            Derivation(
                Eval(
                    Box::new(e.clone()),
                    String::from("evalto"),
                    Box::new(Value0(Box::new(ans))),
                ),
                Box::new(EPlus(d1, d2, d3)),
            ),
        )
    } else {
        panic!()
    }
}

fn derive_eminus(f1: &Fxp, g2: &Gxp, e: &Exp) -> (Value, Derivation) {
    let (ans1, d1) = derive_eval(&Exp1(Box::new(f1.clone())));
    let (ans2, d2) = derive_eval(&Exp1(Box::new(Fxp1(Box::new(g2.clone())))));

    if let (Value0(n1), Value0(n2)) = (ans1, ans2) {
        let (ans, d3) = derive_bminus(&n1, &n2);

        (
            Value0(Box::new(ans.clone())),
            Derivation(
                Eval(
                    Box::new(e.clone()),
                    String::from("evalto"),
                    Box::new(Value0(Box::new(ans))),
                ),
                Box::new(EMinus(d1, d2, d3)),
            ),
        )
    } else {
        panic!()
    }
}

fn derive_etimes(g1: &Gxp, h2: &Hxp, e: &Exp) -> (Value, Derivation) {
    let (ans1, d1) = derive_eval(&Exp1(Box::new(Fxp1(Box::new(g1.clone())))));
    let (ans2, d2) = derive_eval(&Exp1(Box::new(Fxp1(Box::new(Gxp1(Box::new(h2.clone())))))));

    if let (Value0(n1), Value0(n2)) = (ans1, ans2) {
        let (ans, d3) = derive_btimes(&n1, &n2);

        (
            Value0(Box::new(ans.clone())),
            Derivation(
                Eval(
                    Box::new(e.clone()),
                    String::from("evalto"),
                    Box::new(Value0(Box::new(ans))),
                ),
                Box::new(ETimes(d1, d2, d3)),
            ),
        )
    } else {
        panic!()
    }
}

fn derive_elt(f1: &Fxp, e2: &Exp, e: &Exp) -> (Value, Derivation) {
    let (ans1, d1) = derive_eval(&Exp1(Box::new(f1.clone())));
    let (ans2, d2) = derive_eval(e2);

    if let (Value0(n1), Value0(n2)) = (ans1, ans2) {
        let (ans, d3) = derive_blt(&n1, &n2);

        (
            Value1(Box::new(ans.clone())),
            Derivation(
                Eval(
                    Box::new(e.clone()),
                    String::from("evalto"),
                    Box::new(Value1(Box::new(ans))),
                ),
                Box::new(ELt(d1, d2, d3)),
            ),
        )
    } else {
        panic!()
    }
}

fn derive_eval(e: &Exp) -> (Value, Derivation) {
    match e {
        Exp0(f1, _, e2) => derive_elt(f1, e2, e),

        Exp1(f) => match f as &Fxp {
            FxpDummy2(f1, op, g2) => match op as &str {
                "+" => derive_eplus(f1, g2, e),

                "-" => derive_eminus(f1, g2, e),

                _ => panic!(),
            },

            Fxp1(g) => match g as &Gxp {
                GxpDummy2(g1, _, h3) => derive_etimes(g1, h3, e),

                Gxp1(h) => match h as &Hxp {
                    Hxp0(_, e1, _, e2, _, e3) => derive_eif(e1, e2, e3, e),

                    Hxp1(_, e1, _) => derive_eval(e1),

                    Hxp2(n) => derive_eint(n, e),

                    Hxp3(m) => derive_ebool(m, e),
                },

                _ => panic!(),
            },

            _ => panic!(),
        },
    }
}

fn derive(j: &Judgement) -> Derivation {
    match j {
        Eval(e, _, v) => {
            let e = fix_exp(e);
            let (ans, d) = derive_eval(&e);

            if &ans == v as &Value {
                return d;
            }
        }

        Plus(n1, _, n2, _, n3) => {
            let (ans, d) = derive_bplus(n1, n2);

            if &ans == n3 as &Int {
                return d;
            }
        }

        Minus(n1, _, n2, _, n3) => {
            let (ans, d) = derive_bminus(n1, n2);

            if &ans == n3 as &Int {
                return d;
            }
        }

        Times(n1, _, n2, _, n3) => {
            let (ans, d) = derive_btimes(n1, n2);

            if &ans == n3 as &Int {
                return d;
            }
        }

        Lt(n1, _, _, n2, _, n3) => {
            let (ans, d) = derive_blt(n1, n2);

            if &ans == n3 as &Bool {
                return d;
            }
        }
    }

    panic!("Invalid judgement!");
}

fn fix_exp(e: &Exp) -> Exp {
    match e {
        Exp0(f1, s2, e3) => Exp0(Box::new(fix_fxp(f1)), s2.clone(), Box::new(fix_exp(e3))),

        Exp1(f) => Exp1(Box::new(fix_fxp(f))),
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
        Gxp0(h1, s2, g3) => {
            let mut ret = Gxp1(Box::new(fix_hxp(h1)));

            let mut op = s2;

            let mut tmp = g3;

            loop {
                if let Gxp0(h21, s21, g22) = tmp as &Gxp {
                    ret = GxpDummy2(Box::new(ret), op.clone(), Box::new(fix_hxp(h21)));

                    op = s21;

                    tmp = g22;
                } else if let Gxp1(h21) = tmp as &Gxp {
                    ret = GxpDummy2(Box::new(ret), op.clone(), Box::new(fix_hxp(h21)));
                    break;
                } else {
                    panic!("");
                }
            }

            ret
        }

        Gxp1(h) => Gxp1(Box::new(fix_hxp(h))),

        _ => panic!("Invalid!"),
    }
}

fn fix_hxp(h: &Hxp) -> Hxp {
    match h {
        Hxp0(s1, e2, s3, e4, s5, e6) => Hxp0(
            s1.clone(),
            Box::new(fix_exp(e2)),
            s3.clone(),
            Box::new(fix_exp(e4)),
            s5.clone(),
            Box::new(fix_exp(e6)),
        ),

        Hxp1(s1, e2, s3) => Hxp1(s1.clone(), Box::new(fix_exp(e2)), s3.clone()),

        _ => h.clone(),
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
