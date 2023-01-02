mod rule;

use std::{io, ops::Deref};

use self::rule::{
    DBExp, DBFxp, DBGxp, DBHxp, DBIxp, DBJxp, DBLongExp, DBValue, DBValueList, Inner, Judgement,
    Parser, ARROW, COMMA, DBVAR, EQ, EVALTO, FUN, IS, LBRACKET, LESS, LPAREN, MINUS, NUM, PERIOD,
    PLUS, RBRACKET, REC, RPAREN, THAN, TIMES, TRUTH, VDASH,
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
    EVar,
    EIfT(Derivation, Derivation),
    EIfF(Derivation, Derivation),
    EPlus(Derivation, Derivation, Derivation),
    EMinus(Derivation, Derivation, Derivation),
    ETimes(Derivation, Derivation, Derivation),
    ELt(Derivation, Derivation, Derivation),
    ELet(Derivation, Derivation),
    EFun,
    EApp(Derivation, Derivation, Derivation),
    ELetRec(Derivation),
    EAppRec(Derivation, Derivation, Derivation),
    BPlus,
    BMinus,
    BTimes,
    BLt,
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::EInt => write!(f, "E-Int {{}}"),
            Rule::EBool => write!(f, "E-Bool {{}}"),
            Rule::EVar => write!(f, "E-Var {{}}"),
            Rule::EIfT(d0, d1) => write!(f, "E-IfT {{{};{}}}", d0, d1),
            Rule::EIfF(d0, d1) => write!(f, "E-IfF {{{};{}}}", d0, d1),
            Rule::EPlus(d0, d1, d2) => write!(f, "E-Plus {{{};{};{}}}", d0, d1, d2),
            Rule::EMinus(d0, d1, d2) => write!(f, "E-Minus {{{};{};{}}}", d0, d1, d2),
            Rule::ETimes(d0, d1, d2) => write!(f, "E-Times {{{};{};{}}}", d0, d1, d2),
            Rule::ELt(d0, d1, d2) => write!(f, "E-Lt {{{};{};{}}}", d0, d1, d2),
            Rule::ELet(d0, d1) => write!(f, "E-Let {{{};{}}}", d0, d1),
            Rule::EFun => write!(f, "E-Fun {{}}"),
            Rule::EApp(d0, d1, d2) => write!(f, "E-App {{{};{};{}}}", d0, d1, d2),
            Rule::ELetRec(d0) => write!(f, "E-LetRec {{{}}}", d0),
            Rule::EAppRec(d0, d1, d2) => write!(f, "E-AppRec {{{};{};{}}}", d0, d1, d2),
            Rule::BPlus => write!(f, "B-Plus {{}}"),
            Rule::BMinus => write!(f, "B-Minus {{}}"),
            Rule::BTimes => write!(f, "B-Times {{}}"),
            Rule::BLt => write!(f, "B-Lt {{}}"),
        }
    }
}

fn push_dbvaluelist(dbvl: &DBValueList, dbv: &DBValue) -> DBValueList {
    match dbvl {
        DBValueList::DBValueList0(inner) => DBValueList::DBValueList0(Box::new(Inner::Inner0(
            inner.clone(),
            Box::new(COMMA::new(",")),
            Box::new(dbv.clone()),
        ))),
        DBValueList::DBValueList1() => {
            DBValueList::DBValueList0(Box::new(Inner::Inner1(Box::new(dbv.clone()))))
        }
    }
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

fn get_num(v: &DBValue) -> io::Result<i32> {
    if let DBValue::DBValue0(n) = v {
        Ok(n.as_str().parse().unwrap())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        ))
    }
}

fn get_truth(v: &DBValue) -> io::Result<bool> {
    if let DBValue::DBValue1(t) = v {
        Ok(t.as_str().parse().unwrap())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        ))
    }
}

fn eval_dbexp(dbvl: &DBValueList, dbe: &DBExp) -> io::Result<(Derivation, DBValue)> {
    let (rule, dbv) = match dbe {
        DBExp::DBExp0(dble0) => {
            return eval_dblongexp(dbvl, dble0);
        }
        DBExp::DBExp1(dbf0) => {
            return eval_dbfxp(dbvl, dbf0);
        }
        DBExp::DBExp2(dbg0, _ /* < */, dble1) => {
            let (d0, dbv0) = eval_dbgxp(dbvl, dbg0)?;
            let (d1, dbv1) = eval_dblongexp(dbvl, dble1)?;

            let i0 = get_num(&dbv0)?;
            let i1 = get_num(&dbv1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, t) = derive_lt(&n0, &n1)?;

            (Rule::ELt(d0, d1, d2), DBValue::DBValue1(Box::new(t)))
        }
        DBExp::DBExp3(dbg0, _ /* + */, dble1) => {
            let (d0, dbv0) = eval_dbgxp(dbvl, dbg0)?;
            let (d1, dbv1) = eval_dblongexp(dbvl, dble1)?;

            let i0 = get_num(&dbv0)?;
            let i1 = get_num(&dbv1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_plus(&n0, &n1)?;

            (Rule::EPlus(d0, d1, d2), DBValue::DBValue0(Box::new(n)))
        }
        DBExp::DBExp4(dbg0, _ /* - */, dble1) => {
            let (d0, dbv0) = eval_dbgxp(dbvl, dbg0)?;
            let (d1, dbv1) = eval_dblongexp(dbvl, dble1)?;

            let i0 = get_num(&dbv0)?;
            let i1 = get_num(&dbv1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_minus(&n0, &n1)?;

            (Rule::EMinus(d0, d1, d2), DBValue::DBValue0(Box::new(n)))
        }
        DBExp::DBExp5(dbh0, _ /* * */, dble1) => {
            let (d0, dbv0) = eval_dbhxp(dbvl, dbh0)?;
            let (d1, dbv1) = eval_dblongexp(dbvl, dble1)?;

            let i0 = get_num(&dbv0)?;
            let i1 = get_num(&dbv1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_times(&n0, &n1)?;

            (Rule::ETimes(d0, d1, d2), DBValue::DBValue0(Box::new(n)))
        }
    };

    let j = Judgement::Judgement0(
        Box::new(dbvl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(dbe.clone()),
        Box::new(EVALTO::new("evalto")),
        Box::new(dbv.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), dbv))
}

fn eval_dblongexp(dbvl: &DBValueList, dble: &DBLongExp) -> io::Result<(Derivation, DBValue)> {
    let (rule, dbv) = match dble {
        DBLongExp::DBLongExp0(_, dbe0, _, dbe1, _, dbe2) => {
            let (d0, dbv0) = eval_dbexp(dbvl, dbe0)?;

            if get_truth(&dbv0)? {
                let (d1, dbv) = eval_dbexp(dbvl, dbe1)?;
                (Rule::EIfT(d0, d1), dbv)
            } else {
                let (d1, dbv) = eval_dbexp(dbvl, dbe2)?;
                (Rule::EIfF(d0, d1), dbv)
            }
        }

        DBLongExp::DBLongExp1(_, _, _, dbe0, _, dbe1) => {
            let (d0, dbv0) = eval_dbexp(dbvl, dbe0)?;
            let (d1, dbv) = eval_dbexp(&push_dbvaluelist(dbvl, &dbv0), dbe1)?;

            (Rule::ELet(d0, d1), dbv)
        }

        DBLongExp::DBLongExp2(_, _, _, dbe) => (
            Rule::EFun,
            DBValue::DBValue2(
                Box::new(LPAREN::new("(")),
                Box::new(dbvl.clone()),
                Box::new(RPAREN::new(")")),
                Box::new(LBRACKET::new("[")),
                Box::new(FUN::new("fun")),
                Box::new(PERIOD::new(".")),
                Box::new(ARROW::new("->")),
                dbe.clone(),
                Box::new(RBRACKET::new("]")),
            ),
        ),

        DBLongExp::DBLongExp3(_, _, _, _, _, _, _, dbe0, _, dbe1) => {
            let dbv_ = DBValue::DBValue3(
                Box::new(LPAREN::new("(")),
                Box::new(dbvl.clone()),
                Box::new(RPAREN::new(")")),
                Box::new(LBRACKET::new("[")),
                Box::new(REC::new("rec")),
                Box::new(PERIOD::new(".")),
                Box::new(EQ::new("=")),
                Box::new(FUN::new("fun")),
                Box::new(PERIOD::new(".")),
                Box::new(ARROW::new("->")),
                dbe0.clone(),
                Box::new(RBRACKET::new("]")),
            );
            let dbvl_ = push_dbvaluelist(dbvl, &dbv_);
            let (d0, dbv) = eval_dbexp(&dbvl_, dbe1)?;

            (Rule::ELetRec(d0), dbv)
        }
    };

    let j = Judgement::Judgement0(
        Box::new(dbvl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(dble2dbe(dble.clone())),
        Box::new(EVALTO::new("evalto")),
        Box::new(dbv.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), dbv))
}

fn eval_dbfxp(dbvl: &DBValueList, dbf: &DBFxp) -> io::Result<(Derivation, DBValue)> {
    let (rule, dbv) = match dbf {
        DBFxp::DBFxp0(dbg0, _ /* < */, dbg1) => {
            let (d0, dbv0) = eval_dbgxp(dbvl, dbg0)?;
            let (d1, dbv1) = eval_dbgxp(dbvl, dbg1)?;

            let i0 = get_num(&dbv0)?;
            let i1 = get_num(&dbv1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, t) = derive_lt(&n0, &n1)?;

            (Rule::ELt(d0, d1, d2), DBValue::DBValue1(Box::new(t)))
        }

        DBFxp::DBFxp1(dbg0) => {
            return eval_dbgxp(dbvl, dbg0);
        }
    };

    Ok((
        Derivation(
            Judgement::Judgement0(
                Box::new(dbvl.clone()),
                Box::new(VDASH::new("|-")),
                Box::new(dbf2dbe(dbf.clone())),
                Box::new(EVALTO::new("evalto")),
                Box::new(dbv.clone()),
            ),
            Box::new(rule),
        ),
        dbv,
    ))
}

fn eval_dbgxp(dbvl: &DBValueList, dbg: &DBGxp) -> io::Result<(Derivation, DBValue)> {
    let (rule, dbv) = match dbg {
        DBGxp::DBGxp0(dbg0, _ /* + */, dbh1) => {
            let (d0, dbv0) = eval_dbgxp(dbvl, dbg0)?;
            let (d1, dbv1) = eval_dbhxp(dbvl, dbh1)?;

            let i0 = get_num(&dbv0)?;
            let i1 = get_num(&dbv1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_plus(&n0, &n1)?;

            (Rule::EPlus(d0, d1, d2), DBValue::DBValue0(Box::new(n)))
        }

        DBGxp::DBGxp1(dbg0, _ /* - */, dbh1) => {
            let (d0, dbv0) = eval_dbgxp(dbvl, dbg0)?;
            let (d1, dbv1) = eval_dbhxp(dbvl, dbh1)?;

            let i0 = get_num(&dbv0)?;
            let i1 = get_num(&dbv1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_minus(&n0, &n1)?;

            (Rule::EMinus(d0, d1, d2), DBValue::DBValue0(Box::new(n)))
        }

        DBGxp::DBGxp2(dbh0) => {
            return eval_dbhxp(dbvl, dbh0);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(dbvl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(dbf2dbe(dbg2dbf(dbg.clone()))),
        Box::new(EVALTO::new("evalto")),
        Box::new(dbv.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), dbv))
}

fn eval_dbhxp(dbvl: &DBValueList, dbh: &DBHxp) -> io::Result<(Derivation, DBValue)> {
    let (rule, dbv) = match dbh {
        DBHxp::DBHxp0(dbh0, _ /* * */, dbi1) => {
            let (d0, dbv0) = eval_dbhxp(dbvl, dbh0)?;
            let (d1, dbv1) = eval_dbixp(dbvl, dbi1)?;

            let i0 = get_num(&dbv0)?;
            let i1 = get_num(&dbv1)?;
            let n0 = NUM::new(&i0.to_string());
            let n1 = NUM::new(&i1.to_string());

            let (d2, n) = derive_times(&n0, &n1)?;

            (Rule::ETimes(d0, d1, d2), DBValue::DBValue0(Box::new(n)))
        }

        DBHxp::DBHxp1(dbi0) => {
            return eval_dbixp(dbvl, dbi0);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(dbvl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(dbf2dbe(dbg2dbf(dbh2dbg(dbh.clone())))),
        Box::new(EVALTO::new("evalto")),
        Box::new(dbv.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), dbv))
}

fn eval_dbixp(dbvl: &DBValueList, dbi: &DBIxp) -> io::Result<(Derivation, DBValue)> {
    let (rule, dbv) = match dbi {
        DBIxp::DBIxp0(dbi0, dbj1) => {
            let (d0, dbv0) = eval_dbixp(dbvl, dbi0)?;
            let (d1, dbv1) = eval_dbjxp(dbvl, dbj1)?;

            match &dbv0 {
                DBValue::DBValue2(_, dbvl2, _, _, _, _, _, dbe0, _) => {
                    let (d2, dbv) = eval_dbexp(&push_dbvaluelist(dbvl2, &dbv1), dbe0)?;
                    (Rule::EApp(d0, d1, d2), dbv)
                }

                DBValue::DBValue3(_, dbvl2, _, _, _, _, _, _, _, _, dbe0, _) => {
                    let (d2, dbv) = eval_dbexp(
                        &push_dbvaluelist(&push_dbvaluelist(dbvl2, &dbv0), &dbv1),
                        dbe0,
                    )?;

                    (Rule::EAppRec(d0, d1, d2), dbv)
                }

                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!"),
                    ));
                }
            }
        }

        DBIxp::DBIxp1(dbj0) => {
            return eval_dbjxp(dbvl, dbj0);
        }
    };

    let j = Judgement::Judgement0(
        Box::new(dbvl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(dbf2dbe(dbg2dbf(dbh2dbg(dbi2dbh(dbi.clone()))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(dbv.clone()),
    );

    Ok((Derivation(j, Box::new(rule)), dbv))
}

fn eval_dbjxp(dbvl: &DBValueList, dbj: &DBJxp) -> io::Result<(Derivation, DBValue)> {
    match dbj {
        DBJxp::DBJxp0(n) => eval_num(dbvl, n),
        DBJxp::DBJxp1(t) => eval_truth(dbvl, t),
        DBJxp::DBJxp2(x) => eval_dbvar(dbvl, x),
        DBJxp::DBJxp3(_, dbe, _) => eval_dbexp(dbvl, dbe),
    }
}

fn eval_num(dbvl: &DBValueList, n: &NUM) -> io::Result<(Derivation, DBValue)> {
    let dbv = DBValue::DBValue0(Box::new(n.clone()));

    let j = Judgement::Judgement0(
        Box::new(dbvl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(dbf2dbe(dbg2dbf(dbh2dbg(dbi2dbh(dbj2dbi(DBJxp::DBJxp0(
            Box::new(n.clone()),
        ))))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(dbv.clone()),
    );

    Ok((Derivation(j, Box::new(Rule::EInt)), dbv))
}

fn eval_truth(dbvl: &DBValueList, t: &TRUTH) -> io::Result<(Derivation, DBValue)> {
    let dbv = DBValue::DBValue1(Box::new(t.clone()));

    let j = Judgement::Judgement0(
        Box::new(dbvl.clone()),
        Box::new(VDASH::new("|-")),
        Box::new(dbf2dbe(dbg2dbf(dbh2dbg(dbi2dbh(dbj2dbi(DBJxp::DBJxp1(
            Box::new(t.clone()),
        ))))))),
        Box::new(EVALTO::new("evalto")),
        Box::new(dbv.clone()),
    );

    Ok((Derivation(j, Box::new(Rule::EBool)), dbv))
}

fn eval_inner(inner: &Inner, cnt: usize) -> io::Result<DBValue> {
    match inner {
        Inner::Inner0(inner_, _, dbv) => {
            if cnt == 0 {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            } else if cnt == 1 {
                Ok(dbv.deref().clone())
            } else {
                eval_inner(inner_, cnt - 1)
            }
        }

        Inner::Inner1(dbv) => {
            if cnt == 1 {
                Ok(dbv.deref().clone())
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!"),
                ))
            }
        }
    }
}

fn eval_dbvar(dbvl: &DBValueList, x: &DBVAR) -> io::Result<(Derivation, DBValue)> {
    let cnt: usize = x.as_str()[1..].parse().unwrap();

    match dbvl {
        DBValueList::DBValueList0(inner) => {
            let dbv = eval_inner(inner, cnt)?;
            Ok((
                Derivation(
                    Judgement::Judgement0(
                        Box::new(dbvl.clone()),
                        Box::new(VDASH::new("|-")),
                        Box::new(dbf2dbe(dbg2dbf(dbh2dbg(dbi2dbh(dbj2dbi(DBJxp::DBJxp2(
                            Box::new(x.clone()),
                        ))))))),
                        Box::new(EVALTO::new("evalto")),
                        Box::new(dbv.clone()),
                    ),
                    Box::new(Rule::EVar),
                ),
                dbv,
            ))
        }

        DBValueList::DBValueList1() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DerivationError!"),
        )),
    }
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
    match j {
        Judgement::Judgement0(dbvl, _, dbe, _, dbv) => {
            let (d, dbv_) = eval_dbexp(dbvl, dbe)?;

            if dbv.deref() == &dbv_ {
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
