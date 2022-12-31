mod rule;

use std::{io, ops::Deref};

use self::rule::{
    Exp, Fxp, Gxp, Hxp, IfExp, Ixp, Judgement, Parser, Res, Value, ERROR, EVALTO, IS, LESS, MINUS,
    NUM, PLUS, THAN, TIMES, TRUTH,
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
    EPlusBoolL(Derivation),
    EPlusBoolR(Derivation),
    EPlusErrorL(Derivation),
    EPlusErrorR(Derivation),
    EMinusBoolL(Derivation),
    EMinusBoolR(Derivation),
    EMinusErrorL(Derivation),
    EMinusErrorR(Derivation),
    ETimesBoolL(Derivation),
    ETimesBoolR(Derivation),
    ETimesErrorL(Derivation),
    ETimesErrorR(Derivation),
    ELtBoolL(Derivation),
    ELtBoolR(Derivation),
    ELtErrorL(Derivation),
    ELtErrorR(Derivation),
    EIfInt(Derivation),
    EIfError(Derivation),
    EIfTError(Derivation, Derivation),
    EIfFError(Derivation, Derivation),
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::EInt => write!(f, "E-Int {{}}"),
            Rule::EBool => write!(f, "E-Bool {{}}"),
            Rule::EIfT(d0, d1) => write!(f, "E-IfT {{{};{}}}", d0, d1),
            Rule::EIfF(d0, d1) => write!(f, "E-IfF {{{};{}}}", d0, d1),
            Rule::EPlus(d0, d1, d2) => write!(f, "E-Plus {{{};{};{}}}", d0, d1, d2),
            Rule::EMinus(d0, d1, d2) => write!(f, "E-Minus {{{};{};{}}}", d0, d1, d2),
            Rule::ETimes(d0, d1, d2) => write!(f, "E-Times {{{};{};{}}}", d0, d1, d2),
            Rule::ELt(d0, d1, d2) => write!(f, "E-Lt {{{};{};{}}}", d0, d1, d2),
            Rule::BPlus => write!(f, "B-Plus {{}}"),
            Rule::BMinus => write!(f, "B-Minus {{}}"),
            Rule::BTimes => write!(f, "B-Times {{}}"),
            Rule::BLt => write!(f, "B-Lt {{}}"),
            Rule::EPlusBoolL(d0) => write!(f, "E-PlusBoolL {{{}}}", d0),
            Rule::EPlusBoolR(d0) => write!(f, "E-PlusBoolR {{{}}}", d0),
            Rule::EPlusErrorL(d0) => write!(f, "E-PlusErrorL {{{}}}", d0),
            Rule::EPlusErrorR(d0) => write!(f, "E-PlusErrorR {{{}}}", d0),
            Rule::EMinusBoolL(d0) => write!(f, "E-MinusBoolL {{{}}}", d0),
            Rule::EMinusBoolR(d0) => write!(f, "E-MinusBoolR {{{}}}", d0),
            Rule::EMinusErrorL(d0) => write!(f, "E-MinusErrorL {{{}}}", d0),
            Rule::EMinusErrorR(d0) => write!(f, "E-MinusErrorR {{{}}}", d0),
            Rule::ETimesBoolL(d0) => write!(f, "E-TimesBoolL {{{}}}", d0),
            Rule::ETimesBoolR(d0) => write!(f, "E-TimesBoolR {{{}}}", d0),
            Rule::ETimesErrorL(d0) => write!(f, "E-TimesErrorL {{{}}}", d0),
            Rule::ETimesErrorR(d0) => write!(f, "E-TimesErrorR {{{}}}", d0),
            Rule::ELtBoolL(d0) => write!(f, "E-LtBoolL {{{}}}", d0),
            Rule::ELtBoolR(d0) => write!(f, "E-LtBoolR {{{}}}", d0),
            Rule::ELtErrorL(d0) => write!(f, "E-LtErrorL {{{}}}", d0),
            Rule::ELtErrorR(d0) => write!(f, "E-LtErrorR {{{}}}", d0),
            Rule::EIfInt(d0) => write!(f, "E-IfInt {{{}}}", d0),
            Rule::EIfError(d0) => write!(f, "E-IfError {{{}}}", d0),
            Rule::EIfTError(d0, d1) => write!(f, "E-IfTError {{{};{}}}", d0, d1),
            Rule::EIfFError(d0, d1) => write!(f, "E-IfFError {{{};{}}}", d0, d1),
        }
    }
}

enum Response {
    Int(i32),
    Bool(bool),
    Error,
}

fn get_res(r: &Res) -> Response {
    match r {
        Res::Res0(v) => match v.deref() {
            Value::Value0(n) => Response::Int(n.as_str().parse().unwrap()),
            Value::Value1(t) => Response::Bool(t.as_str().parse().unwrap()),
        },
        Res::Res1(_) => Response::Error,
    }
}

fn eval_exp(e: &Exp) -> io::Result<(Derivation, Res)> {
    match e {
        Exp::Exp0(ife) => eval_ifexp(ife),
        Exp::Exp1(f) => eval_fxp(f),
    }
}

fn eval_ifexp(ife: &IfExp) -> io::Result<(Derivation, Res)> {
    let IfExp::IfExp0(_, e0, _, e1, _, e2) = ife;

    let (d0, r0) = eval_exp(e0)?;

    let (rule, r) = match get_res(&r0) {
        Response::Int(_) => (Rule::EIfInt(d0), Res::Res1(Box::new(ERROR::new("error")))),
        Response::Bool(b) => {
            if b {
                let (d1, r) = eval_exp(e1)?;
                if let Response::Error = get_res(&r) {
                    (Rule::EIfTError(d0, d1), r)
                } else {
                    (Rule::EIfT(d0, d1), r)
                }
            } else {
                let (d1, r) = eval_exp(e2)?;

                if let Response::Error = get_res(&r) {
                    (Rule::EIfFError(d0, d1), r)
                } else {
                    (Rule::EIfF(d0, d1), r)
                }
            }
        }
        Response::Error => (Rule::EIfError(d0), Res::Res1(Box::new(ERROR::new("error")))),
    };

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(Exp::Exp0(Box::new(ife.clone()))),
                Box::new(EVALTO::new("evalto")),
                Box::new(r.clone()),
            ),
            Box::new(rule),
        ),
        r,
    ))
}

fn eval_fxp(f: &Fxp) -> io::Result<(Derivation, Res)> {
    let ((d0, r0), (d1, r1)) = match f {
        Fxp::Fxp0(g, _ /* < */, ife) => (eval_gxp(g)?, eval_ifexp(ife)?),

        Fxp::Fxp1(g0, _ /* < */, g1) => (eval_gxp(g0)?, eval_gxp(g1)?),

        Fxp::Fxp2(g) => {
            return eval_gxp(g);
        }
    };

    let (rule, r) = match (get_res(&r0), get_res(&r1)) {
        (Response::Int(i0), Response::Int(i1)) => {
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, t) = derive_lt(&n0, &n1)?;

            (
                Rule::ELt(d0, d1, d2),
                Res::Res0(Box::new(Value::Value1(Box::new(t)))),
            )
        }
        (Response::Bool(_), _) => (Rule::ELtBoolL(d0), Res::Res1(Box::new(ERROR::new("error")))),
        (Response::Error, _) => (
            Rule::ELtErrorL(d0),
            Res::Res1(Box::new(ERROR::new("error"))),
        ),
        (_, Response::Bool(_)) => (Rule::ELtBoolR(d1), Res::Res1(Box::new(ERROR::new("error")))),
        (_, Response::Error) => (
            Rule::ELtErrorR(d1),
            Res::Res1(Box::new(ERROR::new("error"))),
        ),
    };

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(Exp::Exp1(Box::new(f.clone()))),
                Box::new(EVALTO::new("evalto")),
                Box::new(r.clone()),
            ),
            Box::new(rule),
        ),
        r,
    ))
}

fn eval_gxp(g: &Gxp) -> io::Result<(Derivation, Res)> {
    let (rule, r) = match g {
        Gxp::Gxp0(g, _ /* + */, ife) => {
            let (d0, r0) = eval_gxp(g)?;
            let (d1, r1) = eval_ifexp(ife)?;

            match (get_res(&r0), get_res(&r1)) {
                (Response::Int(i0), Response::Int(i1)) => {
                    let n0 = NUM::new(&i0.to_string());
                    let n1 = NUM::new(&i1.to_string());

                    let (d2, n) = derive_plus(&n0, &n1)?;

                    (
                        Rule::EPlus(d0, d1, d2),
                        Res::Res0(Box::new(Value::Value0(Box::new(n)))),
                    )
                }
                (Response::Bool(_), _) => (
                    Rule::EPlusBoolL(d0),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (Response::Error, _) => (
                    Rule::EPlusErrorL(d0),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (_, Response::Bool(_)) => (
                    Rule::EPlusBoolR(d1),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (_, Response::Error) => (
                    Rule::EPlusErrorR(d1),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
            }
        }

        Gxp::Gxp1(g, _ /* - */, ife) => {
            let (d0, r0) = eval_gxp(g)?;
            let (d1, r1) = eval_ifexp(ife)?;
            match (get_res(&r0), get_res(&r1)) {
                (Response::Int(i0), Response::Int(i1)) => {
                    let n0 = NUM::new(&i0.to_string());
                    let n1 = NUM::new(&i1.to_string());

                    let (d2, n) = derive_minus(&n0, &n1)?;

                    (
                        Rule::EMinus(d0, d1, d2),
                        Res::Res0(Box::new(Value::Value0(Box::new(n)))),
                    )
                }
                (Response::Bool(_), _) => (
                    Rule::EMinusBoolL(d0),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (Response::Error, _) => (
                    Rule::EMinusErrorL(d0),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (_, Response::Bool(_)) => (
                    Rule::EMinusBoolR(d1),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (_, Response::Error) => (
                    Rule::EMinusErrorR(d1),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
            }
        }

        Gxp::Gxp2(g, _ /* + */, h) => {
            let (d0, r0) = eval_gxp(g)?;
            let (d1, r1) = eval_hxp(h)?;

            match (get_res(&r0), get_res(&r1)) {
                (Response::Int(i0), Response::Int(i1)) => {
                    let n0 = NUM::new(&i0.to_string());
                    let n1 = NUM::new(&i1.to_string());

                    let (d2, n) = derive_plus(&n0, &n1)?;

                    (
                        Rule::EPlus(d0, d1, d2),
                        Res::Res0(Box::new(Value::Value0(Box::new(n)))),
                    )
                }
                (Response::Bool(_), _) => (
                    Rule::EPlusBoolL(d0),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (Response::Error, _) => (
                    Rule::EPlusErrorL(d0),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (_, Response::Bool(_)) => (
                    Rule::EPlusBoolR(d1),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (_, Response::Error) => (
                    Rule::EPlusErrorR(d1),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
            }
        }

        Gxp::Gxp3(g, _ /* - */, h) => {
            let (d0, r0) = eval_gxp(g)?;
            let (d1, r1) = eval_hxp(h)?;

            match (get_res(&r0), get_res(&r1)) {
                (Response::Int(i0), Response::Int(i1)) => {
                    let n0 = NUM::new(&i0.to_string());
                    let n1 = NUM::new(&i1.to_string());

                    let (d2, n) = derive_minus(&n0, &n1)?;

                    (
                        Rule::EMinus(d0, d1, d2),
                        Res::Res0(Box::new(Value::Value0(Box::new(n)))),
                    )
                }
                (Response::Bool(_), _) => (
                    Rule::EMinusBoolL(d0),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (Response::Error, _) => (
                    Rule::EMinusErrorL(d0),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (_, Response::Bool(_)) => (
                    Rule::EMinusBoolR(d1),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
                (_, Response::Error) => (
                    Rule::EMinusErrorR(d1),
                    Res::Res1(Box::new(ERROR::new("error"))),
                ),
            }
        }

        Gxp::Gxp4(h) => {
            return eval_hxp(h);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(Exp::Exp1(Box::new(Fxp::Fxp2(Box::new(g.clone()))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(r.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), r))
}

fn eval_hxp(h: &Hxp) -> io::Result<(Derivation, Res)> {
    let ((d0, r0), (d1, r1)) = match h {
        Hxp::Hxp0(h, _ /* * */, ife) => (eval_hxp(h)?, eval_ifexp(ife)?),

        Hxp::Hxp1(h, _, i) => (eval_hxp(h)?, eval_ixp(i)?),

        Hxp::Hxp2(i) => {
            return eval_ixp(i);
        }
    };

    let (rule, r) = match (get_res(&r0), get_res(&r1)) {
        (Response::Int(i0), Response::Int(i1)) => {
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_times(&n0, &n1)?;

            (
                Rule::ETimes(d0, d1, d2),
                Res::Res0(Box::new(Value::Value0(Box::new(n)))),
            )
        }
        (Response::Bool(_), _) => (
            Rule::ETimesBoolL(d0),
            Res::Res1(Box::new(ERROR::new("error"))),
        ),
        (Response::Error, _) => (
            Rule::ETimesErrorL(d0),
            Res::Res1(Box::new(ERROR::new("error"))),
        ),
        (_, Response::Bool(_)) => (
            Rule::ETimesBoolR(d1),
            Res::Res1(Box::new(ERROR::new("error"))),
        ),
        (_, Response::Error) => (
            Rule::ETimesErrorR(d1),
            Res::Res1(Box::new(ERROR::new("error"))),
        ),
    };

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(Exp::Exp1(Box::new(Fxp::Fxp2(Box::new(Gxp::Gxp4(
                    Box::new(h.clone()),
                )))))),
                Box::new(EVALTO::new("evalto")),
                Box::new(r.clone()),
            ),
            Box::new(rule),
        ),
        r,
    ))
}

fn eval_ixp(i: &Ixp) -> io::Result<(Derivation, Res)> {
    let (rule, r) = match i {
        Ixp::Ixp0(n) => (Rule::EInt, Res::Res0(Box::new(Value::Value0(n.clone())))),
        Ixp::Ixp1(t) => (Rule::EBool, Res::Res0(Box::new(Value::Value1(t.clone())))),
        Ixp::Ixp2(_, e, _) => {
            return eval_exp(e);
        }
    };

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(Exp::Exp1(Box::new(Fxp::Fxp2(Box::new(Gxp::Gxp4(
                    Box::new(Hxp::Hxp2(Box::new(i.clone()))),
                )))))),
                Box::new(EVALTO::new("evalto")),
                Box::new(r.clone()),
            ),
            Box::new(rule),
        ),
        r,
    ))
}

fn derive_plus(n0: &NUM, n1: &NUM) -> io::Result<(Derivation, NUM)> {
    let i0: i32 = n0.as_str().parse().unwrap();
    let i1: i32 = n1.as_str().parse().unwrap();
    let n2 = NUM::new(&(i0 + i1).to_string());

    let j = Judgement::Judgement1(
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

    let j = Judgement::Judgement2(
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

    let j = Judgement::Judgement3(
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

    let j = Judgement::Judgement4(
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
        Judgement::Judgement0(e, _, r) => {
            let (d, r_) = eval_exp(e)?;
            if r.deref() == &r_ {
                Ok(d)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }

        Judgement::Judgement1(n0, _ /* plus */, n1, _, n2) => {
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

        Judgement::Judgement2(n0, _ /* minus */, n1, _, n2) => {
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

        Judgement::Judgement3(n0, _ /* times */, n1, _, n2) => {
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

        Judgement::Judgement4(n0, _ /* less */, _ /* than */, n1, _, t2) => {
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
