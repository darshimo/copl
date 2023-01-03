mod rule;

use std::{
    cell::{Ref, RefCell},
    fmt::Debug,
    io,
    ops::{Deref, DerefMut},
    rc::Rc,
};

use crate::common;

use self::rule::{
    EType, Exp, Fxp, Gxp, Hxp, Inner, Ixp, Judgement, Jxp, Kxp, LongExp, Parser, TEnv, Type, ARROW,
    BOOL, COLON, COMMA, INT, LIST, LPAREN, NUM, RPAREN, TRUTH, VAR, VDASH,
};

#[derive(Debug)]
struct Derivation(Judgement, Box<Rule>, Capsule<_Type>, _TEnv);
impl std::fmt::Display for Derivation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} by {}", self.0, self.1)
    }
}
impl Derivation {
    fn hoge(&mut self) {
        let Self(Judgement::Judgement0(tenv, _, _, _, t), rule, _t, _tenv) = self;
        *tenv = Box::new(_tenv.to());
        *t = Box::new(_t.myborrow().to());

        match rule.deref_mut() {
            Rule::TInt => {}
            Rule::TBool => {}
            Rule::TVar => {}
            Rule::TIf(d0, d1, d2) => {
                d0.hoge();
                d1.hoge();
                d2.hoge();
            }
            Rule::TPlus(d0, d1) => {
                d0.hoge();
                d1.hoge();
            }
            Rule::TMinus(d0, d1) => {
                d0.hoge();
                d1.hoge();
            }
            Rule::TTimes(d0, d1) => {
                d0.hoge();
                d1.hoge();
            }
            Rule::TLt(d0, d1) => {
                d0.hoge();
                d1.hoge();
            }
            Rule::TLet(d0, d1) => {
                d0.hoge();
                d1.hoge();
            }
            Rule::TFun(d0) => {
                d0.hoge();
            }
            Rule::TApp(d0, d1) => {
                d0.hoge();
                d1.hoge();
            }
            Rule::TLetRec(d0, d1) => {
                d0.hoge();
                d1.hoge();
            }
            Rule::TNil => {}
            Rule::TCons(d0, d1) => {
                d0.hoge();
                d1.hoge();
            }
            Rule::TMatch(d0, d1, d2) => {
                d0.hoge();
                d1.hoge();
                d2.hoge();
            }
        }
    }
}

#[derive(Debug)]
enum Rule {
    TInt,
    TBool,
    TVar,
    TIf(Derivation, Derivation, Derivation),
    TPlus(Derivation, Derivation),
    TMinus(Derivation, Derivation),
    TTimes(Derivation, Derivation),
    TLt(Derivation, Derivation),
    TLet(Derivation, Derivation),
    TFun(Derivation),
    TApp(Derivation, Derivation),
    TLetRec(Derivation, Derivation),
    TNil,
    TCons(Derivation, Derivation),
    TMatch(Derivation, Derivation, Derivation),
}
impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::TInt => write!(f, "T-Int {{}}"),
            Rule::TBool => write!(f, "T-Bool {{}}"),
            Rule::TVar => write!(f, "T-Var {{}}"),
            Rule::TIf(d0, d1, d2) => write!(f, "T-If {{{};{};{}}}", d0, d1, d2),
            Rule::TPlus(d0, d1) => write!(f, "T-Plus {{{};{}}}", d0, d1),
            Rule::TMinus(d0, d1) => write!(f, "T-Minus {{{};{}}}", d0, d1),
            Rule::TTimes(d0, d1) => write!(f, "T-Times {{{};{}}}", d0, d1),
            Rule::TLt(d0, d1) => write!(f, "T-Lt {{{};{}}}", d0, d1),
            Rule::TLet(d0, d1) => write!(f, "T-Let {{{};{}}}", d0, d1),
            Rule::TFun(d0) => write!(f, "T-Fun {{{}}}", d0),
            Rule::TApp(d0, d1) => write!(f, "T-App {{{};{}}}", d0, d1),
            Rule::TLetRec(d0, d1) => write!(f, "T-LetRec {{{};{}}}", d0, d1),
            Rule::TNil => write!(f, "T-Nil {{}}"),
            Rule::TCons(d0, d1) => write!(f, "T-Cons {{{};{}}}", d0, d1),
            Rule::TMatch(d0, d1, d2) => write!(f, "T-Match {{{};{};{}}}", d0, d1, d2),
        }
    }
}

#[derive(Debug, Clone)]
struct Capsule<T>(Rc<RefCell<T>>);
impl<T: Clone + Debug> Capsule<T> {
    fn new(x: T) -> Self {
        Self(Rc::new(RefCell::new(x)))
    }

    fn myborrow(&self) -> Ref<T> {
        RefCell::borrow(&self.0)
    }

    fn replace(&self, x: Self) {
        *RefCell::borrow_mut(&self.0) = (&*x.myborrow()).clone();
    }
}
impl Capsule<_Type> {
    fn make_dummy() -> Self {
        Capsule::new(_Type::_Type1(Capsule::new(_EType::Dummy(Capsule::new(
            Err(common::get_id()),
        )))))
    }

    fn make_func(t0: Self, t1: Self) -> Self {
        match &*t0.myborrow() {
            _Type::_Type0(ft) => Capsule::new(_Type::_Type0(Capsule::new(_FType::_FType0(
                ft.clone(),
                t1.clone(),
            )))),
            _Type::_Type1(et) => Capsule::new(_Type::_Type0(Capsule::new(_FType::_FType1(
                et.clone(),
                t1.clone(),
            )))),
        }
    }

    fn make_int() -> Self {
        Capsule::new(_Type::_Type1(Capsule::new(_EType::Int)))
    }

    fn make_bool() -> Self {
        Capsule::new(_Type::_Type1(Capsule::new(_EType::Bool)))
    }

    fn make_list(t: Self) -> Self {
        match &*t.myborrow() {
            _Type::_Type0(ft) => {
                Capsule::new(_Type::_Type1(Capsule::new(_EType::FList(ft.clone()))))
            }
            _Type::_Type1(et) => {
                Capsule::new(_Type::_Type1(Capsule::new(_EType::EList(et.clone()))))
            }
        }
    }

    fn from(t: &Type) -> Self {
        match t {
            Type::Type0(et0, _, t1) => {
                Capsule::make_func(Capsule::from(&Type::Type1(et0.clone())), Capsule::from(t1))
            }

            Type::Type1(et0) => match et0.deref() {
                EType::EType0(_) => Capsule::make_int(),

                EType::EType1(_) => Capsule::make_bool(),

                EType::EType2(et0_, _) => {
                    Capsule::make_list(Capsule::from(&Type::Type1(et0_.clone())))
                }

                EType::EType3(_, t_, _) => Self::from(t_),
            },
        }
    }
}

#[derive(Debug, Clone)]
enum _Type {
    _Type0(Capsule<_FType>),
    _Type1(Capsule<_EType>),
}
impl _Type {
    fn merge(t0: Capsule<_Type>, t1: Capsule<_Type>) -> io::Result<()> {
        let c: Box<dyn FnOnce() -> io::Result<()>> = match (&*t0.myborrow(), &*t1.myborrow()) {
            (_Type::_Type0(ft0), _Type::_Type0(ft1)) => {
                let a = ft0.clone();
                let b = ft1.clone();

                Box::new(|| _FType::merge(a, b))
            }

            (_Type::_Type1(et0), _Type::_Type1(et1)) => {
                let a = et0.clone();
                let b = et1.clone();

                Box::new(|| _EType::merge(a, b))
            }

            (_Type::_Type0(_), _Type::_Type1(et1)) => {
                if let _EType::Dummy(op) = &*et1.myborrow() {
                    match &*op.myborrow() {
                        Ok(tmp) => {
                            let a = t0.clone();
                            let b = tmp.clone();

                            Box::new(|| {
                                // t1.replace(t0.clone());
                                // Ok(())
                                _Type::merge(a, b)
                            })
                        }
                        Err(_) => {
                            let a = Capsule::new(Ok(t0.clone()));
                            let b = op.clone();

                            Box::new(move || {
                                // t1.replace(t0.clone());
                                b.replace(a);
                                Ok(())
                            })
                        }
                    }
                } else {
                    Box::new(|| {
                        Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            format!("DerivationError!0"),
                        ))
                    })
                }
            }

            (_Type::_Type1(et0), _Type::_Type0(_)) => {
                if let _EType::Dummy(op) = &*et0.myborrow() {
                    match &*op.myborrow() {
                        Ok(tmp) => {
                            let a = tmp.clone();
                            let b = t1.clone();

                            Box::new(|| {
                                // t0.replace(t1.clone());
                                // Ok(())
                                _Type::merge(a, b)
                            })
                        }
                        Err(_) => {
                            let a = op.clone();
                            let b = Capsule::new(Ok(t1.clone()));

                            Box::new(move || {
                                // t0.replace(t1.clone());
                                a.replace(b);
                                Ok(())
                            })
                        }
                    }
                } else {
                    Box::new(|| {
                        Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            format!("DerivationError!1"),
                        ))
                    })
                }
            }
        };

        c()
    }

    fn to(&self) -> Type {
        match self {
            _Type::_Type0(ft) => ft.myborrow().to(),

            _Type::_Type1(et) => Type::Type1(Box::new(et.myborrow().to())),
        }
    }
}

#[derive(Debug, Clone)]
enum _EType {
    Int,
    Bool,
    EList(Capsule<_EType>),
    FList(Capsule<_FType>),
    Dummy(Capsule<Result<Capsule<_Type>, u32>>),
}
impl _EType {
    fn merge(et0: Capsule<_EType>, et1: Capsule<_EType>) -> io::Result<()> {
        let c: Box<dyn FnOnce() -> io::Result<()>> = match (&*et0.myborrow(), &*et1.myborrow()) {
            (_EType::Int, _EType::Int) => Box::new(|| Ok(())),

            (_EType::Bool, _EType::Bool) => Box::new(|| Ok(())),

            (_EType::EList(et0_), _EType::EList(et1_)) => {
                let a = et0_.clone();
                let b = et1_.clone();
                Box::new(|| _EType::merge(a, b))
            }

            (_EType::FList(ft0), _EType::FList(ft1)) => {
                let a = ft0.clone();
                let b = ft1.clone();
                Box::new(|| _FType::merge(a, b))
            }

            (_EType::Dummy(op0), _EType::Dummy(op1)) => {
                match (&*op0.myborrow(), &*op1.myborrow()) {
                    (&Err(id0), &Err(id1)) => {
                        if id0 == id1 {
                            Box::new(|| Ok(()))
                        } else {
                            let a = op0.clone();
                            let b = Capsule::new(Ok(Capsule::new(_Type::_Type1(et1.clone()))));

                            Box::new(move || {
                                // et0.replace(et1.clone());
                                a.replace(b);

                                Ok(())
                            })
                        }
                    }

                    (Ok(tmp0), Ok(tmp1)) => {
                        let a = tmp0.clone();
                        let b = tmp1.clone();

                        Box::new(move || _Type::merge(a, b))
                    }

                    (Err(_), Ok(tmp1)) => {
                        let a = op0.clone();
                        // let b = Capsule::new(Ok(Capsule::new(_Type::_Type1(et1.clone()))));
                        let b = Capsule::new(Ok(tmp1.clone()));

                        Box::new(move || {
                            // et0.replace(et1.clone());
                            a.replace(b);

                            Ok(())
                        })
                    }

                    (Ok(tmp0), Err(_)) => {
                        // let a = Capsule::new(Ok(Capsule::new(_Type::_Type1(et0.clone()))));
                        let a = Capsule::new(Ok(tmp0.clone()));
                        let b = op1.clone();

                        Box::new(move || {
                            // et0.replace(et1.clone());
                            b.replace(a);

                            Ok(())
                        })
                    }
                }
            }

            (_EType::Dummy(op), _ /* not dummy */) => match &*op.myborrow() {
                Ok(tmp) => {
                    let a = tmp.clone();
                    let b = Capsule::new(_Type::_Type1(et1.clone()));

                    Box::new(|| {
                        // et0.replace(et1.clone());
                        // Ok(())

                        _Type::merge(a, b)
                    })
                }
                Err(_) => {
                    let a = op.clone();
                    let b = Capsule::new(Ok(Capsule::new(_Type::_Type1(et1.clone()))));

                    Box::new(move || {
                        // et0.replace(et1.clone());
                        a.replace(b);

                        Ok(())
                    })
                }
            },

            (_ /* not dummy */, _EType::Dummy(op)) => match &*op.myborrow() {
                Ok(tmp) => {
                    let a = Capsule::new(_Type::_Type1(et0.clone()));
                    let b = tmp.clone();

                    Box::new(|| {
                        // et1.replace(et0.clone());
                        // Ok(())

                        _Type::merge(a, b)
                    })
                }
                Err(_) => {
                    let a = Capsule::new(Ok(Capsule::new(_Type::_Type1(et0.clone()))));
                    let b = op.clone();

                    Box::new(move || {
                        // et1.replace(et0.clone());
                        b.replace(a);

                        Ok(())
                    })
                }
            },

            _ => Box::new(|| {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!2"),
                ))
            }),
        };

        c()
    }

    fn to(&self) -> EType {
        match self {
            _EType::Int => EType::EType0(Box::new(INT::new("int"))),

            _EType::Bool => EType::EType1(Box::new(BOOL::new("bool"))),

            _EType::EList(et) => {
                EType::EType2(Box::new(et.myborrow().to()), Box::new(LIST::new("list")))
            }

            _EType::FList(ft) => EType::EType2(
                Box::new(EType::EType3(
                    Box::new(LPAREN::new("(")),
                    Box::new(ft.myborrow().to()),
                    Box::new(RPAREN::new(")")),
                )),
                Box::new(LIST::new("list")),
            ),

            _EType::Dummy(op) => match &*op.myborrow() {
                Ok(tmp) => {
                    let t = tmp.myborrow().to();
                    match &t {
                        Type::Type0(_, _, _) => EType::EType3(
                            Box::new(LPAREN::new("(")),
                            Box::new(t.clone()),
                            Box::new(RPAREN::new(")")),
                        ),

                        Type::Type1(et) => et.deref().clone(),
                    }
                }

                Err(_) => EType::EType1(Box::new(BOOL::new("bool"))),
            },
        }
    }
}

#[derive(Debug, Clone)]
enum _FType {
    _FType0(Capsule<_FType>, Capsule<_Type>),
    _FType1(Capsule<_EType>, Capsule<_Type>),
}
impl _FType {
    fn merge(ft0: Capsule<_FType>, ft1: Capsule<_FType>) -> io::Result<()> {
        let c: Box<dyn FnOnce() -> io::Result<()>> = match (&*ft0.myborrow(), &*ft1.myborrow()) {
            (_FType::_FType0(ft0_, t0_), _FType::_FType0(ft1_, t1_)) => {
                let a = ft0_.clone();
                let b = ft1_.clone();
                let c = t0_.clone();
                let d = t1_.clone();

                Box::new(|| {
                    _FType::merge(a, b)?;
                    _Type::merge(c, d)?;
                    Ok(())
                })
            }

            (_FType::_FType1(et0_, t0_), _FType::_FType1(et1_, t1_)) => {
                let a = et0_.clone();
                let b = et1_.clone();
                let c = t0_.clone();
                let d = t1_.clone();

                Box::new(|| {
                    _EType::merge(a, b)?;
                    _Type::merge(c, d)?;
                    Ok(())
                })
            }

            (_FType::_FType0(ft0_, t0_), _FType::_FType1(et1_, t1_)) => {
                if let _EType::Dummy(op) = &*et1_.myborrow() {
                    match &*op.myborrow() {
                        Ok(tmp) => {
                            let a = Capsule::new(_Type::_Type0(ft0_.clone()));
                            let b = tmp.clone();

                            let c = t0_.clone();
                            let d = t1_.clone();

                            Box::new(|| {
                                _Type::merge(a, b)?;
                                _Type::merge(c, d)?;
                                Ok(())
                            })
                        }
                        Err(_) => {
                            let a = Capsule::new(Ok(Capsule::new(_Type::_Type0(ft0_.clone()))));
                            let b = op.clone();

                            let c = t0_.clone();
                            let d = t1_.clone();

                            Box::new(move || {
                                b.replace(a);
                                _Type::merge(c, d)?;
                                //     ft1.replace(ft0.clone());
                                Ok(())
                            })
                        }
                    }
                } else {
                    Box::new(|| {
                        Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            format!("DerivationError!2"),
                        ))
                    })
                }
            }

            (_FType::_FType1(et0_, t0_), _FType::_FType0(ft1_, t1_)) => {
                if let _EType::Dummy(op) = &*et0_.myborrow() {
                    match &*op.myborrow() {
                        Ok(tmp) => {
                            let a = tmp.clone();
                            let b = Capsule::new(_Type::_Type0(ft1_.clone()));

                            let c = t0_.clone();
                            let d = t1_.clone();

                            Box::new(|| {
                                _Type::merge(a, b)?;
                                _Type::merge(c, d)?;
                                Ok(())
                            })
                        }
                        Err(_) => {
                            let a = op.clone();
                            let b = Capsule::new(Ok(Capsule::new(_Type::_Type0(ft1_.clone()))));

                            let c = t0_.clone();
                            let d = t1_.clone();

                            Box::new(move || {
                                a.replace(b);
                                _Type::merge(c, d)?;
                                //     ft0.replace(ft1.clone());
                                Ok(())
                            })
                        }
                    }
                } else {
                    Box::new(|| {
                        Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            format!("DerivationError!2"),
                        ))
                    })
                }
            }
        };

        c()
    }

    fn to(&self) -> Type {
        match self {
            _FType::_FType0(ft, t) => Type::Type0(
                Box::new(EType::EType3(
                    Box::new(LPAREN::new("(")),
                    Box::new(ft.myborrow().to()),
                    Box::new(RPAREN::new(")")),
                )),
                Box::new(ARROW::new("->")),
                Box::new(t.myborrow().to()),
            ),

            _FType::_FType1(et, t) => Type::Type0(
                Box::new(et.myborrow().to()),
                Box::new(ARROW::new("->")),
                Box::new(t.myborrow().to()),
            ),
        }
    }
}

#[derive(Debug, Clone)]
enum _TEnv {
    _TEnv0(Box<_TEnv>, VAR, Capsule<_Type>),
    _TEnv1(),
}
impl _TEnv {
    fn push(&self, x: &VAR, t: Capsule<_Type>) -> Self {
        _TEnv::_TEnv0(Box::new(self.clone()), x.clone(), t.clone())
    }

    fn from(tenv: &TEnv) -> Self {
        match tenv {
            TEnv::TEnv0(inner) => match inner.deref() {
                Inner::Inner0(inner_, _, x, _, t) => _TEnv::_TEnv0(
                    Box::new(_TEnv::from(&TEnv::TEnv0(inner_.clone()))),
                    x.deref().clone(),
                    Capsule::from(t),
                ),

                Inner::Inner1(x, _, t) => _TEnv::_TEnv0(
                    Box::new(_TEnv::_TEnv1()),
                    x.deref().clone(),
                    Capsule::from(t),
                ),
            },

            TEnv::TEnv1() => _TEnv::_TEnv1(),
        }
    }

    fn to(&self) -> TEnv {
        match self {
            _TEnv::_TEnv0(tenv, x, t) => match tenv.to() {
                TEnv::TEnv0(inner) => TEnv::TEnv0(Box::new(Inner::Inner0(
                    inner,
                    Box::new(COMMA::new(",")),
                    Box::new(x.clone()),
                    Box::new(COLON::new(":")),
                    Box::new(t.myborrow().to()),
                ))),

                TEnv::TEnv1() => TEnv::TEnv0(Box::new(Inner::Inner1(
                    Box::new(x.clone()),
                    Box::new(COLON::new(":")),
                    Box::new(t.myborrow().to()),
                ))),
            },

            _TEnv::_TEnv1() => TEnv::TEnv1(),
        }
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
    Gxp::Gxp1(Box::new(h))
}

fn i2h(i: Ixp) -> Hxp {
    Hxp::Hxp2(Box::new(i))
}

fn j2i(j: Jxp) -> Ixp {
    Ixp::Ixp1(Box::new(j))
}

fn k2j(k: Kxp) -> Jxp {
    Jxp::Jxp1(Box::new(k))
}

fn eval_exp(tenv: &_TEnv, e: &Exp, t: Capsule<_Type>) -> io::Result<Derivation> {
    let (rule, _t) = match e {
        Exp::Exp0(le) => {
            return eval_longexp(tenv, le, t);
        }
        Exp::Exp1(f) => {
            return eval_fxp(tenv, f, t);
        }
        Exp::Exp2(g, _ /* < */, le) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_gxp(tenv, g, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_longexp(tenv, le, t1.clone())?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TLt(d0, d1), Capsule::make_bool())
        }
        Exp::Exp3(h, _ /* :: */, le) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_hxp(tenv, h, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_longexp(tenv, le, t1.clone())?;

            let () = _Type::merge(Capsule::make_list(t0), t1.clone())?;

            (Rule::TCons(d0, d1), t1)
        }
        Exp::Exp4(h, _ /* + */, le) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_hxp(tenv, h, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_longexp(tenv, le, t1.clone())?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TPlus(d0, d1), Capsule::make_int())
        }
        Exp::Exp5(h, _ /* - */, le) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_hxp(tenv, h, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_longexp(tenv, le, t1.clone())?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TMinus(d0, d1), Capsule::make_int())
        }
        Exp::Exp6(i, _ /* * */, le) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_ixp(tenv, i, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_longexp(tenv, le, t1.clone())?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TTimes(d0, d1), Capsule::make_int())
        }
    };

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(e.clone()),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn eval_longexp(tenv: &_TEnv, le: &LongExp, t: Capsule<_Type>) -> io::Result<Derivation> {
    let (rule, _t) = match le {
        LongExp::LongExp0(_, e0, _, e1, _, e2) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_exp(tenv, e0, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_exp(tenv, e1, t1.clone())?;

            let t2 = Capsule::make_dummy();
            let d2 = eval_exp(tenv, e2, t2.clone())?;

            let () = _Type::merge(t0, Capsule::make_bool())?;
            let () = _Type::merge(t1.clone(), t2)?;

            (Rule::TIf(d0, d1, d2), t1)
        }

        LongExp::LongExp1(_, x, _, e0, _, e1) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_exp(tenv, e0, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_exp(&tenv.push(x, t0), e1, t1.clone())?;

            (Rule::TLet(d0, d1), t1)
        }

        LongExp::LongExp2(_, x, _, e) => {
            let t0 = Capsule::make_dummy();
            let t1 = Capsule::make_dummy();
            let d0 = eval_exp(&tenv.push(x, t0.clone()), e, t1.clone())?;

            (Rule::TFun(d0), Capsule::make_func(t0, t1))
        }

        LongExp::LongExp3(_, _, x, _, _, y, _, e0, _, e1) => {
            let t0 = Capsule::make_dummy();
            let t1 = Capsule::make_dummy();
            let _t = Capsule::make_dummy();

            let d0 = eval_exp(
                &tenv
                    .push(x, Capsule::make_func(t0.clone(), t1.clone()))
                    .push(y, t0.clone()),
                e0,
                t1.clone(),
            )?;
            let d1 = eval_exp(&tenv.push(x, Capsule::make_func(t0, t1)), e1, _t.clone())?;

            (Rule::TLetRec(d0, d1), _t)
        }

        LongExp::LongExp4(_, e0, _, _, _, _, e1, _, x, _, y, _, e2) => {
            let t_ = Capsule::make_dummy();
            let d0 = eval_exp(tenv, e0, Capsule::make_list(t_.clone()))?;

            let _t = Capsule::make_dummy();
            let d1 = eval_exp(tenv, e1, _t.clone())?;

            let d2 = eval_exp(
                &tenv.push(x, t_.clone()).push(y, Capsule::make_list(t_)),
                e2,
                _t.clone(),
            )?;

            (Rule::TMatch(d0, d1, d2), _t)
        }
    };

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(le2e(le.clone())),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn eval_fxp(tenv: &_TEnv, f: &Fxp, t: Capsule<_Type>) -> io::Result<Derivation> {
    let (rule, _t) = match f {
        Fxp::Fxp0(g0, _ /* < */, g1) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_gxp(tenv, g0, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_gxp(tenv, g1, t1.clone())?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TLt(d0, d1), Capsule::make_bool())
        }

        Fxp::Fxp1(g) => {
            return eval_gxp(tenv, g, t);
        }
    };

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(f.clone())),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn eval_gxp(tenv: &_TEnv, g: &Gxp, t: Capsule<_Type>) -> io::Result<Derivation> {
    let (rule, _t) = match g {
        Gxp::Gxp0(h, _ /* :: */, g) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_hxp(tenv, h, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_gxp(tenv, g, t1.clone())?;

            let () = _Type::merge(Capsule::make_list(t0), t1.clone())?;

            (Rule::TCons(d0, d1), t1)
        }

        Gxp::Gxp1(h) => {
            return eval_hxp(tenv, h, t);
        }
    };

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(g.clone()))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn eval_hxp(tenv: &_TEnv, h: &Hxp, t: Capsule<_Type>) -> io::Result<Derivation> {
    let (rule, _t) = match h {
        Hxp::Hxp0(h, _ /* + */, i) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_hxp(tenv, h, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_ixp(tenv, i, t1.clone())?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TPlus(d0, d1), Capsule::make_int())
        }

        Hxp::Hxp1(h, _ /* - */, i) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_hxp(tenv, h, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_ixp(tenv, i, t1.clone())?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TMinus(d0, d1), Capsule::make_int())
        }

        Hxp::Hxp2(i) => {
            return eval_ixp(tenv, i, t);
        }
    };

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(h.clone())))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn eval_ixp(tenv: &_TEnv, i: &Ixp, t: Capsule<_Type>) -> io::Result<Derivation> {
    let (rule, _t) = match i {
        Ixp::Ixp0(i, _ /* * */, j) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_ixp(tenv, i, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_jxp(tenv, j, t1.clone())?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TTimes(d0, d1), Capsule::make_int())
        }

        Ixp::Ixp1(j) => {
            return eval_jxp(tenv, j, t);
        }
    };

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(i.clone()))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn eval_jxp(tenv: &_TEnv, j: &Jxp, t: Capsule<_Type>) -> io::Result<Derivation> {
    let (rule, _t) = match j {
        Jxp::Jxp0(j0, k1) => {
            let t0 = Capsule::make_dummy();
            let d0 = eval_jxp(tenv, j0, t0.clone())?;

            let t1 = Capsule::make_dummy();
            let d1 = eval_kxp(tenv, k1, t1.clone())?;

            let _t = Capsule::make_dummy();

            let () = _Type::merge(t0, Capsule::make_func(t1, _t.clone()))?;

            (Rule::TApp(d0, d1), _t)
        }

        Jxp::Jxp1(k) => {
            return eval_kxp(tenv, k, t);
        }
    };

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(j.clone())))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn eval_kxp(tenv: &_TEnv, k: &Kxp, t: Capsule<_Type>) -> io::Result<Derivation> {
    let (rule, _t) = match k {
        Kxp::Kxp0(n) => {
            return eval_num(tenv, n, t);
        }
        Kxp::Kxp1(x) => {
            return eval_truth(tenv, x, t);
        }
        Kxp::Kxp2(x) => {
            return eval_var(tenv, x, t);
        }
        Kxp::Kxp3(_, _) => {
            let _t = Capsule::make_list(Capsule::make_dummy());

            (Rule::TNil, _t)
        }
        Kxp::Kxp4(_, e, _) => {
            return eval_exp(tenv, e, t);
        }
    };

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(k2j(k.clone()))))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn eval_var(tenv: &_TEnv, x: &VAR, t: Capsule<_Type>) -> io::Result<Derivation> {
    fn find(tenv: &_TEnv, x: &VAR) -> io::Result<Capsule<_Type>> {
        match tenv {
            _TEnv::_TEnv0(tenv_, y, _t) => {
                if x == y {
                    Ok(_t.clone())
                } else {
                    find(tenv_, x)
                }
            }

            _TEnv::_TEnv1() => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("DerivationError!4"),
            )),
        }
    }

    let (rule, _t) = (Rule::TVar, find(tenv, x)?);

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(k2j(Kxp::Kxp2(Box::new(x.clone()))))))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn eval_num(tenv: &_TEnv, n: &NUM, t: Capsule<_Type>) -> io::Result<Derivation> {
    let (rule, _t) = (Rule::TInt, Capsule::make_int());

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(k2j(Kxp::Kxp0(Box::new(n.clone()))))))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn eval_truth(tenv: &_TEnv, x: &TRUTH, t: Capsule<_Type>) -> io::Result<Derivation> {
    let (rule, _t) = (Rule::TBool, Capsule::make_bool());

    _Type::merge(t, _t.clone())?;

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(k2j(Kxp::Kxp1(Box::new(x.clone()))))))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok(Derivation(j, Box::new(rule), _t, tenv.clone()))
}

fn derive(j: &Judgement) -> io::Result<Derivation> {
    let Judgement::Judgement0(tenv, _, e, _, t) = j;

    let _t = Capsule::from(t);

    let _tenv = _TEnv::from(tenv);

    let mut d = eval_exp(&_tenv, e, _t)?;

    d.hoge();

    Ok(d)
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
