mod rule;

use std::{io, ops::Deref};

use self::rule::{
    DBExp, DBFxp, DBGxp, DBHxp, DBIxp, DBJxp, DBLongExp, Exp, Fxp, Gxp, Hxp, Inner, Ixp, Judgement,
    Jxp, LongExp, Parser, VarList, ARROW, AST, COMMA, CROSS, DBVAR, ELSE, EQ, FUN, HYPHEN, IF, IN,
    LET, LPAREN, LT, PERIOD, REC, RPAREN, THEN, TRANS, VAR, VDASH,
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
    TrInt,
    TrBool,
    TrVar1,
    TrVar2(Derivation),
    TrIf(Derivation, Derivation, Derivation),
    TrPlus(Derivation, Derivation),
    TrMinus(Derivation, Derivation),
    TrTimes(Derivation, Derivation),
    TrLt(Derivation, Derivation),
    TrLet(Derivation, Derivation),
    TrFun(Derivation),
    TrApp(Derivation, Derivation),
    TrLetRec(Derivation, Derivation),
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::TrInt => write!(f, "Tr-Int {{}}"),
            Rule::TrBool => write!(f, "Tr-Bool {{}}"),
            Rule::TrVar1 => write!(f, "Tr-Var1 {{}}"),
            Rule::TrVar2(d0) => write!(f, "Tr-Var2 {{{}}}", d0),
            Rule::TrIf(d0, d1, d2) => write!(f, "Tr-If {{{};{};{}}}", d0, d1, d2),
            Rule::TrPlus(d0, d1) => write!(f, "Tr-Plus {{{};{}}}", d0, d1),
            Rule::TrMinus(d0, d1) => write!(f, "Tr-Minus {{{};{}}}", d0, d1),
            Rule::TrTimes(d0, d1) => write!(f, "Tr-Times {{{};{}}}", d0, d1),
            Rule::TrLt(d0, d1) => write!(f, "Tr-Lt {{{};{}}}", d0, d1),
            Rule::TrLet(d0, d1) => write!(f, "Tr-Let {{{};{}}}", d0, d1),
            Rule::TrFun(d0) => write!(f, "Tr-Fun {{{}}}", d0),
            Rule::TrApp(d0, d1) => write!(f, "Tr-App {{{};{}}}", d0, d1),
            Rule::TrLetRec(d0, d1) => write!(f, "Tr-LetRec {{{};{}}}", d0, d1),
        }
    }
}

fn push_varlist(vl: &VarList, x: &VAR) -> VarList {
    match vl {
        VarList::VarList0(inner) => VarList::VarList0(Box::new(Inner::Inner0(
            inner.clone(),
            Box::new(COMMA::new(",")),
            Box::new(x.clone()),
        ))),
        VarList::VarList1() => VarList::VarList0(Box::new(Inner::Inner1(Box::new(x.clone())))),
    }
}

fn le2e(le: LongExp) -> Exp {
    Exp::Exp0(Box::new(le))
}

fn f2e(f: Fxp) -> Exp {
    Exp::Exp1(Box::new(f))
}

fn g2f(g: Gxp) -> Fxp {
    Fxp::Fxp1(Box::new(g))
}

fn h2g(h: Hxp) -> Gxp {
    Gxp::Gxp2(Box::new(h))
}

fn i2h(i: Ixp) -> Hxp {
    Hxp::Hxp1(Box::new(i))
}

fn j2i(j: Jxp) -> Ixp {
    Ixp::Ixp1(Box::new(j))
}

fn dble2dbe(dble: DBLongExp) -> DBExp {
    DBExp::DBExp0(Box::new(dble))
}

fn dbf2dbe(dbf: DBFxp) -> DBExp {
    DBExp::DBExp1(Box::new(dbf))
}

fn dbg2dbf(dbg: DBGxp) -> DBFxp {
    DBFxp::DBFxp1(Box::new(dbg))
}

fn dbh2dbg(dbh: DBHxp) -> DBGxp {
    DBGxp::DBGxp2(Box::new(dbh))
}

fn dbi2dbh(dbi: DBIxp) -> DBHxp {
    DBHxp::DBHxp1(Box::new(dbi))
}

fn dbj2dbi(dbj: DBJxp) -> DBIxp {
    DBIxp::DBIxp1(Box::new(dbj))
}

fn eval_exp(vl: &VarList, e: &Exp) -> io::Result<(Derivation, DBExp)> {
    let (rule, dbe) = match e {
        Exp::Exp0(le) => {
            let (d, dble) = eval_longexp(vl, le)?;
            return Ok((d, DBExp::DBExp0(Box::new(dble))));
        }
        Exp::Exp1(f) => {
            let (d, dbf) = eval_fxp(vl, f)?;
            return Ok((d, DBExp::DBExp1(Box::new(dbf))));
        }
        Exp::Exp2(g, _ /* < */, le) => {
            let (d0, dbg0) = eval_gxp(vl, g)?;
            let (d1, dble1) = eval_longexp(vl, le)?;
            (
                Rule::TrLt(d0, d1),
                DBExp::DBExp2(Box::new(dbg0), Box::new(LT::new("<")), Box::new(dble1)),
            )
        }
        Exp::Exp3(g, _ /* + */, le) => {
            let (d0, dbg) = eval_gxp(vl, g)?;
            let (d1, dble) = eval_longexp(vl, le)?;
            (
                Rule::TrPlus(d0, d1),
                DBExp::DBExp3(Box::new(dbg), Box::new(CROSS::new("+")), Box::new(dble)),
            )
        }
        Exp::Exp4(g, _ /* - */, le) => {
            let (d0, dbg) = eval_gxp(vl, g)?;
            let (d1, dble) = eval_longexp(vl, le)?;
            (
                Rule::TrPlus(d0, d1),
                DBExp::DBExp4(Box::new(dbg), Box::new(HYPHEN::new("-")), Box::new(dble)),
            )
        }
        Exp::Exp5(h, _ /* * */, le) => {
            let (d0, dbh) = eval_hxp(vl, h)?;
            let (d1, dble) = eval_longexp(vl, le)?;
            (
                Rule::TrTimes(d0, d1),
                DBExp::DBExp5(Box::new(dbh), Box::new(AST::new("*")), Box::new(dble)),
            )
        }
    };

    let j = Judgement::Judgement0(
        Box::new(vl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(e.clone()),
        Box::new(TRANS::new("==>")),
        Box::new(dbe.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), dbe))
}

fn eval_longexp(vl: &VarList, le: &LongExp) -> io::Result<(Derivation, DBLongExp)> {
    let (rule, dble) = match le {
        LongExp::LongExp0(_, e0, _, e1, _, e2) => {
            let (d0, dbe0) = eval_exp(vl, e0)?;
            let (d1, dbe1) = eval_exp(vl, e1)?;
            let (d2, dbe2) = eval_exp(vl, e2)?;

            (
                Rule::TrIf(d0, d1, d2),
                DBLongExp::DBLongExp0(
                    Box::new(IF::new("if")),
                    Box::new(dbe0),
                    Box::new(THEN::new("then")),
                    Box::new(dbe1),
                    Box::new(ELSE::new("else")),
                    Box::new(dbe2),
                ),
            )
        }

        LongExp::LongExp1(_, x, _, e0, _, e1) => {
            let (d0, dbe0) = eval_exp(vl, e0)?;
            let (d1, dbe1) = eval_exp(&push_varlist(vl, x), e1)?;

            (
                Rule::TrLet(d0, d1),
                DBLongExp::DBLongExp1(
                    Box::new(LET::new("let")),
                    Box::new(PERIOD::new(".")),
                    Box::new(EQ::new("=")),
                    Box::new(dbe0),
                    Box::new(IN::new("in")),
                    Box::new(dbe1),
                ),
            )
        }

        LongExp::LongExp2(_, x, _, e) => {
            let (d0, dbe0) = eval_exp(&push_varlist(vl, x), e)?;

            (
                Rule::TrFun(d0),
                DBLongExp::DBLongExp2(
                    Box::new(FUN::new("fun")),
                    Box::new(PERIOD::new(".")),
                    Box::new(ARROW::new("->")),
                    Box::new(dbe0),
                ),
            )
        }

        LongExp::LongExp3(_, _, x, _, _, y, _, e0, _, e1) => {
            let vl1 = push_varlist(vl, x);
            let vl0 = push_varlist(&vl1, y);
            let (d0, dbe0) = eval_exp(&vl0, e0)?;
            let (d1, dbe1) = eval_exp(&vl1, e1)?;

            (
                Rule::TrLetRec(d0, d1),
                DBLongExp::DBLongExp3(
                    Box::new(LET::new("let")),
                    Box::new(REC::new("rec")),
                    Box::new(PERIOD::new(".")),
                    Box::new(EQ::new("=")),
                    Box::new(FUN::new("fun")),
                    Box::new(PERIOD::new(".")),
                    Box::new(ARROW::new("->")),
                    Box::new(dbe0),
                    Box::new(IN::new("in")),
                    Box::new(dbe1),
                ),
            )
        }
    };

    let j = Judgement::Judgement0(
        Box::new(vl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(le2e(le.clone())),
        Box::new(TRANS::new("==>")),
        Box::new(dble2dbe(dble.clone())),
    );

    Ok((Derivation(j, Box::new(rule)), dble))
}

fn eval_fxp(vl: &VarList, f: &Fxp) -> io::Result<(Derivation, DBFxp)> {
    let (rule, dbf) = match f {
        Fxp::Fxp0(g0, _ /* < */, g1) => {
            let (d0, dbg0) = eval_gxp(vl, g0)?;
            let (d1, dbg1) = eval_gxp(vl, g1)?;

            (
                Rule::TrLt(d0, d1),
                DBFxp::DBFxp0(Box::new(dbg0), Box::new(LT::new("<")), Box::new(dbg1)),
            )
        }

        Fxp::Fxp1(g0) => {
            let (d0, dbg0) = eval_gxp(vl, g0)?;
            return Ok((d0, dbg2dbf(dbg0)));
        }
    };

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(vl.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(Exp::Exp1(Box::new(f.clone()))),
                Box::new(TRANS::new("==>")),
                Box::new(dbf2dbe(dbf.clone())),
            ),
            Box::new(rule),
        ),
        dbf,
    ))
}

fn eval_gxp(vl: &VarList, g: &Gxp) -> io::Result<(Derivation, DBGxp)> {
    let (rule, dbg) = match g {
        Gxp::Gxp0(g0, _ /* + */, h1) => {
            let (d0, dbg0) = eval_gxp(vl, g0)?;
            let (d1, dbh1) = eval_hxp(vl, h1)?;

            (
                Rule::TrPlus(d0, d1),
                DBGxp::DBGxp0(Box::new(dbg0), Box::new(CROSS::new("+")), Box::new(dbh1)),
            )
        }

        Gxp::Gxp1(g0, _ /* - */, h1) => {
            let (d0, dbg0) = eval_gxp(vl, g0)?;
            let (d1, dbh1) = eval_hxp(vl, h1)?;

            (
                Rule::TrMinus(d0, d1),
                DBGxp::DBGxp1(Box::new(dbg0), Box::new(HYPHEN::new("-")), Box::new(dbh1)),
            )
        }

        Gxp::Gxp2(h0) => {
            let (d0, dbh0) = eval_hxp(vl, h0)?;

            return Ok((d0, dbh2dbg(dbh0)));
        }
    };

    let j = Judgement::Judgement0(
        Box::new(vl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(g.clone()))),
        Box::new(TRANS::new("==>")),
        Box::new(dbf2dbe(dbg2dbf(dbg.clone()))),
    );

    Ok((Derivation(j, Box::new(rule)), dbg))
}

fn eval_hxp(vl: &VarList, h: &Hxp) -> io::Result<(Derivation, DBHxp)> {
    let (rule, dbh) = match h {
        Hxp::Hxp0(h0, _ /* * */, i1) => {
            let (d0, dbh0) = eval_hxp(vl, h0)?;
            let (d1, dbi1) = eval_ixp(vl, i1)?;

            (
                Rule::TrTimes(d0, d1),
                DBHxp::DBHxp0(Box::new(dbh0), Box::new(AST::new("*")), Box::new(dbi1)),
            )
        }

        Hxp::Hxp1(i0) => {
            let (d0, dbi) = eval_ixp(vl, i0)?;
            return Ok((d0, dbi2dbh(dbi)));
        }
    };

    let j = Judgement::Judgement0(
        Box::new(vl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(h.clone())))),
        Box::new(TRANS::new("==>")),
        Box::new(dbf2dbe(dbg2dbf(dbh2dbg(dbh.clone())))),
    );

    Ok((Derivation(j, Box::new(rule)), dbh))
}

fn eval_ixp(vl: &VarList, i: &Ixp) -> io::Result<(Derivation, DBIxp)> {
    let (rule, dbi) = match i {
        Ixp::Ixp0(i0, j1) => {
            let (d0, dbi0) = eval_ixp(vl, i0)?;
            let (d1, dbj1) = eval_jxp(vl, j1)?;

            (
                Rule::TrApp(d0, d1),
                DBIxp::DBIxp0(Box::new(dbi0), Box::new(dbj1)),
            )
        }

        Ixp::Ixp1(j0) => {
            let (d0, dbj0) = eval_jxp(vl, j0)?;

            return Ok((d0, dbj2dbi(dbj0)));
        }
    };

    let j = Judgement::Judgement0(
        Box::new(vl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(i.clone()))))),
        Box::new(TRANS::new("==>")),
        Box::new(dbf2dbe(dbg2dbf(dbh2dbg(dbi2dbh(dbi.clone()))))),
    );

    Ok((Derivation(j, Box::new(rule)), dbi))
}

fn eval_jxp(vl: &VarList, j: &Jxp) -> io::Result<(Derivation, DBJxp)> {
    let (rule, dbj) = match j {
        Jxp::Jxp0(n) => {
            let dbj = DBJxp::DBJxp0(n.clone());
            (Rule::TrInt, dbj)
        }

        Jxp::Jxp1(t) => {
            let dbj = DBJxp::DBJxp1(t.clone());
            (Rule::TrBool, dbj)
        }

        Jxp::Jxp2(x) => {
            let (d, dbv) = eval_var(vl, x)?;
            return Ok((d, DBJxp::DBJxp2(Box::new(dbv))));
        }

        Jxp::Jxp3(_, e, _) => {
            let (d, dbe) = eval_exp(vl, e)?;
            return Ok((
                d,
                DBJxp::DBJxp3(
                    Box::new(LPAREN::new("(")),
                    Box::new(dbe),
                    Box::new(RPAREN::new(")")),
                ),
            ));
        }
    };

    let j = Judgement::Judgement0(
        Box::new(vl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(j.clone())))))),
        Box::new(TRANS::new("==>")),
        Box::new(dbf2dbe(dbg2dbf(dbh2dbg(dbi2dbh(dbj2dbi(dbj.clone())))))),
    );

    Ok((Derivation(j, Box::new(rule)), dbj))
}

fn eval_inner(inner: &Inner, x: &VAR) -> io::Result<(Derivation, usize)> {
    let (rule, n) = match inner {
        Inner::Inner0(inner_, _, y) => {
            if x == y.deref() {
                (Rule::TrVar1, 1)
            } else {
                let (d0, n) = eval_inner(&inner_, x)?;
                (Rule::TrVar2(d0), n + 1)
            }
        }
        Inner::Inner1(y) => {
            if x == y.deref() {
                (Rule::TrVar1, 1)
            } else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ));
            }
        }
    };

    let dbv = DBVAR::new(&format!("#{}", n));

    let j = Judgement::Judgement0(
        Box::new(VarList::VarList0(Box::new(inner.clone()))),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(Jxp::Jxp2(Box::new(x.clone())))))))),
        Box::new(TRANS::new("==>")),
        Box::new(dbf2dbe(dbg2dbf(dbh2dbg(dbi2dbh(dbj2dbi(DBJxp::DBJxp2(
            Box::new(dbv.clone()),
        ))))))),
    );

    Ok((Derivation(j, Box::new(rule)), n))
}

fn eval_var(vl: &VarList, x: &VAR) -> io::Result<(Derivation, DBVAR)> {
    match vl {
        VarList::VarList0(inner) => {
            let (d, n) = eval_inner(inner, x)?;
            let dbv = DBVAR::new(&format!("#{}", n));
            Ok((d, dbv))
        }
        VarList::VarList1() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        )),
    }
}

fn derive(j: &Judgement) -> io::Result<Derivation> {
    let Judgement::Judgement0(vl, _, e, _, dbe) = j;

    let (d, dbe_) = eval_exp(vl, e)?;

    if dbe.deref() == &dbe_ {
        Ok(d)
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        ))
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
