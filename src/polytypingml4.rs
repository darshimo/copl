mod rule;

use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    io,
    ops::{Deref, DerefMut},
    rc::Rc,
};

use crate::common;

use self::rule::{
    EType, Exp, Fxp, Gxp, Hxp, Inner, Ixp, Judgement, Jxp, Kxp, LongExp, Parser, TEnv, TVarList,
    TyScheme, Type, ARROW, BOOL, COLON, COMMA, INT, LIST, LPAREN, NUM, PERIOD, RPAREN, TRUTH, TVAR,
    VAR, VDASH,
};

impl Hash for TVAR {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

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
        *t = Box::new(_t.to());

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
            Rule::TAbs(d0) => {
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
    TAbs(Derivation),
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
            Rule::TAbs(d0) => write!(f, "T-Abs {{{}}}", d0),
            Rule::TApp(d0, d1) => write!(f, "T-App {{{};{}}}", d0, d1),
            Rule::TLetRec(d0, d1) => write!(f, "T-LetRec {{{};{}}}", d0, d1),
            Rule::TNil => write!(f, "T-Nil {{}}"),
            Rule::TCons(d0, d1) => write!(f, "T-Cons {{{};{}}}", d0, d1),
            Rule::TMatch(d0, d1, d2) => write!(f, "T-Match {{{};{};{}}}", d0, d1, d2),
        }
    }
}

impl Type {
    fn normalize(&self) -> Self {
        match self {
            Type::Type0(et0, _, t1) => {
                let et0_ = et0.normalize();
                let mut t1_ = t1.normalize();

                if let Type::Type1(et1) = &mut t1_ {
                    if let EType::EType3(_, t_, _) = et1.deref_mut() {
                        let t1_ = std::mem::replace(
                            t_.deref_mut(),
                            Type::Type1(Box::new(EType::EType0(Box::new(INT::new("hoge"))))),
                        );

                        return Type::Type0(
                            Box::new(et0_),
                            Box::new(ARROW::new("->")),
                            Box::new(t1_),
                        );
                    }
                }

                Type::Type0(Box::new(et0_), Box::new(ARROW::new("->")), Box::new(t1_))
            }

            Type::Type1(et0) => {
                let mut et0_ = et0.normalize();

                if let EType::EType3(_, t_, _) = &mut et0_ {
                    let t1_ = std::mem::replace(
                        t_.deref_mut(),
                        Type::Type1(Box::new(EType::EType0(Box::new(INT::new("hoge"))))),
                    );

                    return t1_;
                }

                Type::Type1(Box::new(et0_))
            }
        }
    }
}

impl EType {
    fn normalize(&self) -> Self {
        match self {
            EType::EType0(_) | EType::EType1(_) | EType::EType4(_) => self.clone(),

            EType::EType2(et, _) => {
                EType::EType2(Box::new(et.normalize()), Box::new(LIST::new("list")))
            }

            EType::EType3(_, t, _) => EType::EType3(
                Box::new(LPAREN::new("(")),
                Box::new(t.normalize()),
                Box::new(RPAREN::new(")")),
            ),
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

            (_Type::_Type0(_), _Type::_Type1(et1)) => match &*et1.myborrow() {
                _EType::Dummy(op) => match &*op.myborrow() {
                    Ok(tmp) => {
                        let a = t0.clone();
                        let b = tmp.clone();

                        Box::new(|| _Type::merge(a, b))
                    }
                    Err(_) => {
                        let a = Capsule::new(Ok(t0.clone()));
                        let b = op.clone();

                        Box::new(move || {
                            b.replace(a);
                            Ok(())
                        })
                    }
                },

                _ => Box::new(|| {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!0"),
                    ))
                }),
            },

            (_Type::_Type1(et0), _Type::_Type0(_)) => match &*et0.myborrow() {
                _EType::Dummy(op) => match &*op.myborrow() {
                    Ok(tmp) => {
                        let a = tmp.clone();
                        let b = t1.clone();

                        Box::new(|| _Type::merge(a, b))
                    }
                    Err(_) => {
                        let a = op.clone();
                        let b = Capsule::new(Ok(t1.clone()));

                        Box::new(move || {
                            a.replace(b);
                            Ok(())
                        })
                    }
                },

                _ => Box::new(|| {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!1"),
                    ))
                }),
            },
        };

        c()
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

    fn from_tv(tv: &TVAR) -> Self {
        Capsule::new(_Type::_Type1(Capsule::new(_EType::TVar(tv.clone()))))
    }

    fn to_sub(&self) -> Type {
        match &*self.myborrow() {
            _Type::_Type0(ft) => ft.to_sub(),
            _Type::_Type1(et) => Type::Type1(Box::new(et.to_sub())),
        }
    }

    fn to(&self) -> Type {
        self.to_sub().normalize()
    }

    fn from(t: &Type) -> Self {
        match t {
            Type::Type0(et0, _, t1) => {
                let tmp1 = Capsule::from(&t1);

                let tmp0 = match et0.deref() {
                    EType::EType0(_) => Capsule::make_int(),
                    EType::EType1(_) => Capsule::make_bool(),
                    EType::EType2(tmp, _) => Capsule::make_list(Capsule::from(&Type::Type1(
                        Box::new(tmp.deref().clone()),
                    ))),
                    EType::EType3(_, tmp, _) => Capsule::from(tmp),
                    EType::EType4(tv) => Capsule::from_tv(tv),
                };

                Capsule::make_func(tmp0, tmp1)
            }

            Type::Type1(et0) => match et0.deref() {
                EType::EType0(_) => Capsule::make_int(),
                EType::EType1(_) => Capsule::make_bool(),
                EType::EType2(tmp, _) => {
                    Capsule::make_list(Capsule::from(&Type::Type1(Box::new(tmp.deref().clone()))))
                }
                EType::EType3(_, tmp, _) => Capsule::from(tmp),
                EType::EType4(tv) => Capsule::from_tv(tv),
            },
        }
    }

    fn instantiate(&self, btv_map: &HashMap<u32, Capsule<Result<Capsule<_Type>, u32>>>) -> Self {
        match &*self.myborrow() {
            _Type::_Type0(ft) => Capsule::new(_Type::_Type0(ft.instantiate(btv_map))),
            _Type::_Type1(et) => Capsule::new(_Type::_Type1(et.instantiate(btv_map))),
        }
    }

    fn schemize(
        &self,
        ftv_set: &HashSet<u32>,
        btv_map: &mut HashMap<u32, (u32, Capsule<Result<Capsule<_Type>, u32>>)>,
    ) -> Self {
        match &*self.myborrow() {
            _Type::_Type0(ft) => Capsule::new(_Type::_Type0(ft.schemize(ftv_set, btv_map))),
            _Type::_Type1(et) => Capsule::new(_Type::_Type1(et.schemize(ftv_set, btv_map))),
        }
    }

    fn fuga(&self, btv_map: &HashMap<TVAR, (u32, Capsule<Result<Capsule<_Type>, u32>>)>) -> Self {
        match &*self.myborrow() {
            _Type::_Type0(ft) => Capsule::new(_Type::_Type0(ft.fuga(btv_map))),
            _Type::_Type1(et) => Capsule::new(_Type::_Type1(et.fuga(btv_map))),
        }
    }

    fn get_all_tv(&self) -> HashSet<u32> {
        match &*self.myborrow() {
            _Type::_Type0(ft) => ft.get_all_tv(),
            _Type::_Type1(et) => et.get_all_tv(),
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
    TVar(TVAR),
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

            (_EType::FList(ft0_), _EType::EList(et1_)) => match &*et1_.myborrow() {
                _EType::Dummy(op) => match &*op.myborrow() {
                    Ok(tmp) => {
                        let a = Capsule::new(_Type::_Type0(ft0_.clone()));
                        let b = tmp.clone();

                        Box::new(|| {
                            _Type::merge(a, b)?;
                            Ok(())
                        })
                    }
                    Err(_) => {
                        let a = Capsule::new(Ok(Capsule::new(_Type::_Type0(ft0_.clone()))));
                        let b = op.clone();

                        Box::new(move || {
                            b.replace(a);
                            Ok(())
                        })
                    }
                },

                _ => Box::new(|| {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!03"),
                    ))
                }),
            },

            (_EType::EList(et0_), _EType::FList(ft1_)) => match &*et0_.myborrow() {
                _EType::Dummy(op) => match &*op.myborrow() {
                    Ok(tmp) => {
                        let a = tmp.clone();
                        let b = Capsule::new(_Type::_Type0(ft1_.clone()));

                        Box::new(|| {
                            _Type::merge(a, b)?;
                            Ok(())
                        })
                    }
                    Err(_) => {
                        let a = op.clone();
                        let b = Capsule::new(Ok(Capsule::new(_Type::_Type0(ft1_.clone()))));

                        Box::new(move || {
                            a.replace(b);
                            Ok(())
                        })
                    }
                },

                _ => Box::new(|| {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!04"),
                    ))
                }),
            },

            (_EType::TVar(tv0), _EType::TVar(tv1)) => {
                if tv0.as_str() == tv1.as_str() {
                    Box::new(|| Ok(()))
                } else {
                    Box::new(|| {
                        Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            format!("DerivationError!01"),
                        ))
                    })
                }
            }

            (_EType::Dummy(op0), _EType::Dummy(op1)) => {
                match (&*op0.myborrow(), &*op1.myborrow()) {
                    (Err(id0), Err(id1)) => {
                        if id0 == id1 {
                            Box::new(|| Ok(()))
                        } else {
                            let a = op0.clone();
                            let b = Capsule::new(Ok(Capsule::new(_Type::_Type1(et1.clone()))));

                            Box::new(move || {
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
                        let a = Capsule::new(_Type::_Type1(et0.clone()));
                        let b = tmp1.clone();

                        Box::new(move || {
                            _Type::merge(a, b)?;

                            Ok(())
                        })
                    }

                    (Ok(tmp0), Err(_)) => {
                        let a = tmp0.clone();
                        let b = Capsule::new(_Type::_Type1(et1.clone()));

                        Box::new(move || {
                            _Type::merge(a, b)?;

                            Ok(())
                        })
                    }
                }
            }

            (_EType::Dummy(op), _ /* not dummy */) => match &*op.myborrow() {
                Ok(tmp) => {
                    let a = tmp.clone();
                    let b = Capsule::new(_Type::_Type1(et1.clone()));

                    Box::new(|| _Type::merge(a, b))
                }
                Err(_) => {
                    let a = op.clone();
                    let b = Capsule::new(Ok(Capsule::new(_Type::_Type1(et1.clone()))));

                    Box::new(move || {
                        a.replace(b);

                        Ok(())
                    })
                }
            },

            (_ /* not dummy */, _EType::Dummy(op)) => match &*op.myborrow() {
                Ok(tmp) => {
                    let a = Capsule::new(_Type::_Type1(et0.clone()));
                    let b = tmp.clone();

                    Box::new(|| _Type::merge(a, b))
                }
                Err(_) => {
                    let a = Capsule::new(Ok(Capsule::new(_Type::_Type1(et0.clone()))));
                    let b = op.clone();

                    Box::new(move || {
                        b.replace(a);

                        Ok(())
                    })
                }
            },

            _ => Box::new(|| {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("DerivationError!02"),
                ))
            }),
        };

        c()
    }
}
impl Capsule<_EType> {
    fn to_sub(&self) -> EType {
        match &*self.myborrow() {
            _EType::Int => EType::EType0(Box::new(INT::new("int"))),
            _EType::Bool => EType::EType1(Box::new(BOOL::new("bool"))),
            _EType::TVar(tv) => EType::EType4(Box::new(tv.clone())),
            _EType::EList(et) => EType::EType2(Box::new(et.to_sub()), Box::new(LIST::new("list"))),
            _EType::FList(ft) => EType::EType2(
                Box::new(EType::EType3(
                    Box::new(LPAREN::new("(")),
                    Box::new(ft.to_sub()),
                    Box::new(RPAREN::new(")")),
                )),
                Box::new(LIST::new("list")),
            ),
            _EType::Dummy(op) => match &*op.myborrow() {
                Ok(tmp) => {
                    let t = tmp.to_sub();
                    match &t {
                        Type::Type0(_, _, _) => EType::EType3(
                            Box::new(LPAREN::new("(")),
                            Box::new(t),
                            Box::new(RPAREN::new(")")),
                        ),
                        Type::Type1(et) => et.deref().clone(),
                    }
                }
                Err(i) => EType::EType4(Box::new(TVAR::new(&format!("'t{}", i)))),
            },
        }
    }

    fn instantiate(&self, btv_map: &HashMap<u32, Capsule<Result<Capsule<_Type>, u32>>>) -> Self {
        match &*self.myborrow() {
            _EType::Int | _EType::Bool | _EType::TVar(_) => self.clone(),

            _EType::EList(et) => Capsule::new(_EType::EList(et.instantiate(btv_map))),

            _EType::FList(ft) => Capsule::new(_EType::FList(ft.instantiate(btv_map))),

            _EType::Dummy(op) => match &*op.myborrow() {
                Ok(t) => Capsule::new(_EType::Dummy(Capsule::new(Ok(t.instantiate(btv_map))))),

                Err(i) => {
                    if let Some(tmp) = btv_map.get(i) {
                        Capsule::new(_EType::Dummy(tmp.clone()))
                    } else {
                        self.clone()
                    }
                }
            },
        }
    }

    fn schemize(
        &self,
        ftv_set: &HashSet<u32>,
        btv_map: &mut HashMap<u32, (u32, Capsule<Result<Capsule<_Type>, u32>>)>,
    ) -> Self {
        match &*self.myborrow() {
            _EType::Int | _EType::Bool | _EType::TVar(_) => self.clone(),

            _EType::EList(et) => Capsule::new(_EType::EList(et.schemize(ftv_set, btv_map))),

            _EType::FList(ft) => Capsule::new(_EType::FList(ft.schemize(ftv_set, btv_map))),

            _EType::Dummy(op) => match &*op.myborrow() {
                Ok(tmp) => Capsule::new(_EType::Dummy(Capsule::new(Ok(
                    tmp.schemize(ftv_set, btv_map)
                )))),

                Err(i) => {
                    if ftv_set.contains(i) {
                        self.clone()
                    } else if let Some((_, tmp)) = btv_map.get(i) {
                        Capsule::new(_EType::Dummy(tmp.clone()))
                    } else {
                        let j = common::get_id();
                        let tmp = Capsule::new(Err(j));
                        btv_map.insert(*i, (j, tmp.clone()));
                        Capsule::new(_EType::Dummy(tmp))
                    }
                }
            },
        }
    }

    fn fuga(&self, btv_map: &HashMap<TVAR, (u32, Capsule<Result<Capsule<_Type>, u32>>)>) -> Self {
        match &*self.myborrow() {
            _EType::Int | _EType::Bool => self.clone(),

            _EType::EList(et) => Capsule::new(_EType::EList(et.fuga(btv_map))),

            _EType::FList(ft) => Capsule::new(_EType::FList(ft.fuga(btv_map))),

            _EType::Dummy(_) => panic!(),

            _EType::TVar(tv) => {
                if let Some((_, tmp)) = btv_map.get(tv) {
                    Capsule::new(_EType::Dummy(tmp.clone()))
                } else {
                    self.clone()
                }
            }
        }
    }

    fn get_all_tv(&self) -> HashSet<u32> {
        match &*self.myborrow() {
            _EType::Int | _EType::Bool | _EType::TVar(_) => HashSet::new(),
            _EType::FList(ft) => ft.get_all_tv(),
            _EType::EList(et) => et.get_all_tv(),
            _EType::Dummy(op) => match &*op.myborrow() {
                Ok(tmp) => tmp.get_all_tv(),
                Err(i) => HashSet::from([*i]),
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

            (_FType::_FType0(ft0_, t0_), _FType::_FType1(et1_, t1_)) => match &*et1_.myborrow() {
                _EType::Dummy(op) => match &*op.myborrow() {
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
                            Ok(())
                        })
                    }
                },

                _ => Box::new(|| {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!03"),
                    ))
                }),
            },

            (_FType::_FType1(et0_, t0_), _FType::_FType0(ft1_, t1_)) => match &*et0_.myborrow() {
                _EType::Dummy(op) => match &*op.myborrow() {
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
                            Ok(())
                        })
                    }
                },

                _ => Box::new(|| {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("DerivationError!04"),
                    ))
                }),
            },
        };

        c()
    }
}

impl Capsule<_FType> {
    fn to_sub(&self) -> Type {
        match &*self.myborrow() {
            _FType::_FType0(ft, t) => Type::Type0(
                Box::new(EType::EType3(
                    Box::new(LPAREN::new("(")),
                    Box::new(ft.to_sub()),
                    Box::new(RPAREN::new(")")),
                )),
                Box::new(ARROW::new("->")),
                Box::new(t.to_sub()),
            ),

            _FType::_FType1(et, t) => Type::Type0(
                Box::new(et.to_sub()),
                Box::new(ARROW::new("->")),
                Box::new(t.to_sub()),
            ),
        }
    }

    fn instantiate(&self, btv_map: &HashMap<u32, Capsule<Result<Capsule<_Type>, u32>>>) -> Self {
        match &*self.myborrow() {
            _FType::_FType0(ft, t) => Capsule::new(_FType::_FType0(
                ft.instantiate(btv_map),
                t.instantiate(btv_map),
            )),

            _FType::_FType1(et, t) => Capsule::new(_FType::_FType1(
                et.instantiate(btv_map),
                t.instantiate(btv_map),
            )),
        }
    }

    fn schemize(
        &self,
        ftv_set: &HashSet<u32>,
        btv_map: &mut HashMap<u32, (u32, Capsule<Result<Capsule<_Type>, u32>>)>,
    ) -> Self {
        match &*self.myborrow() {
            _FType::_FType0(ft, t) => Capsule::new(_FType::_FType0(
                ft.schemize(ftv_set, btv_map),
                t.schemize(ftv_set, btv_map),
            )),
            _FType::_FType1(et, t) => Capsule::new(_FType::_FType1(
                et.schemize(ftv_set, btv_map),
                t.schemize(ftv_set, btv_map),
            )),
        }
    }

    fn fuga(&self, btv_map: &HashMap<TVAR, (u32, Capsule<Result<Capsule<_Type>, u32>>)>) -> Self {
        match &*self.myborrow() {
            _FType::_FType0(ft, t) => {
                Capsule::new(_FType::_FType0(ft.fuga(btv_map), t.fuga(btv_map)))
            }
            _FType::_FType1(et, t) => {
                Capsule::new(_FType::_FType1(et.fuga(btv_map), t.fuga(btv_map)))
            }
        }
    }

    fn get_all_tv(&self) -> HashSet<u32> {
        match &*self.myborrow() {
            _FType::_FType0(ft, t) => ft.get_all_tv().union(&t.get_all_tv()).map(|i| *i).collect(),
            _FType::_FType1(et, t) => et.get_all_tv().union(&t.get_all_tv()).map(|i| *i).collect(),
        }
    }
}

#[derive(Debug, Clone)]
struct _TyScheme(Vec<u32>, Capsule<_Type>);
impl _TyScheme {
    fn from(ts: &TyScheme) -> Self {
        match ts {
            TyScheme::TyScheme0(tvl, _, t) => {
                fn f(tvl: &TVarList) -> Vec<(TVAR, u32)> {
                    match tvl {
                        TVarList::TVarList0(tvl_, tv) => {
                            let mut v1 = f(&tvl_);
                            let tmp = tv.deref().clone();
                            if !v1.iter().any(|(tv_, _)| tv_ == &tmp) {
                                v1.push((tmp, common::get_id()));
                            }
                            v1
                        }

                        TVarList::TVarList1(tv) => vec![(tv.deref().clone(), common::get_id())],
                    }
                }

                let btv_vec = f(tvl);

                let btv_map = btv_vec
                    .iter()
                    .map(|(tv, i)| (tv.clone(), (*i, Capsule::new(Err(*i)))))
                    .collect();

                let t = Capsule::from(t).fuga(&btv_map);

                _TyScheme(btv_vec.into_iter().map(|(_, x)| x).collect(), t)
            }

            TyScheme::TyScheme1(t) => {
                let btv_vec: Vec<(TVAR, u32)> = vec![];

                let btv_map = btv_vec
                    .iter()
                    .map(|(tv, i)| (tv.clone(), (*i, Capsule::new(Err(*i)))))
                    .collect();

                let t = Capsule::from(t).fuga(&btv_map);

                _TyScheme(btv_vec.into_iter().map(|(_, x)| x).collect(), t)
            }
        }
    }

    fn to(&self) -> TyScheme {
        let _TyScheme(btv_set, _t) = self;

        let t = _t.to();

        let mut btv_iter = btv_set.into_iter();

        if let Some(btv) = btv_iter.next() {
            let mut tvl = TVarList::TVarList1(Box::new(TVAR::new(&format!("'t{}", btv))));

            while let Some(btv) = btv_iter.next() {
                let tmp =
                    TVarList::TVarList0(Box::new(tvl), Box::new(TVAR::new(&format!("'t{}", btv))));
                tvl = tmp;
            }

            TyScheme::TyScheme0(Box::new(tvl), Box::new(PERIOD::new(".")), Box::new(t))
        } else {
            TyScheme::TyScheme1(Box::new(t))
        }
    }

    fn get_btv(&self) -> HashSet<u32> {
        self.0.iter().map(|x| *x).collect()
    }

    fn get_ftv(&self) -> HashSet<u32> {
        self.1
            .get_all_tv()
            .difference(&self.get_btv())
            .map(|i| *i)
            .collect()
    }

    fn instantiate(&self) -> Capsule<_Type> {
        let btv_map = self
            .get_btv()
            .iter()
            .map(|i| (*i, Capsule::new(Err(common::get_id()))))
            .collect();
        self.1.instantiate(&btv_map)
    }

    fn schemize(t: Capsule<_Type>, tenv: &_TEnv) -> _TyScheme {
        let ftv_set = tenv.get_ftv();
        let mut btv_map = HashMap::new();
        let t_ = t.schemize(&ftv_set, &mut btv_map);
        _TyScheme(btv_map.into_iter().map(|(_, (i, _))| i).collect(), t_)
    }
}

#[derive(Debug, Clone)]
enum _TEnv {
    _TEnv0(Box<_TEnv>, VAR, _TyScheme),
    _TEnv1(),
}
impl _TEnv {
    fn push(&self, x: &VAR, _ts: _TyScheme) -> Self {
        _TEnv::_TEnv0(Box::new(self.clone()), x.clone(), _ts.clone())
    }

    fn from(tenv: &TEnv) -> Self {
        match tenv {
            TEnv::TEnv0(inner) => match inner.deref() {
                Inner::Inner0(inner_, _, x, _, ts) => _TEnv::_TEnv0(
                    Box::new(_TEnv::from(&TEnv::TEnv0(inner_.clone()))),
                    x.deref().clone(),
                    _TyScheme::from(ts),
                ),

                Inner::Inner1(x, _, ts) => _TEnv::_TEnv0(
                    Box::new(_TEnv::_TEnv1()),
                    x.deref().clone(),
                    _TyScheme::from(ts),
                ),
            },

            TEnv::TEnv1() => _TEnv::_TEnv1(),
        }
    }

    fn to(&self) -> TEnv {
        match self {
            _TEnv::_TEnv0(tenv, x, ts) => match tenv.to() {
                TEnv::TEnv0(inner) => TEnv::TEnv0(Box::new(Inner::Inner0(
                    inner,
                    Box::new(COMMA::new(",")),
                    Box::new(x.clone()),
                    Box::new(COLON::new(":")),
                    Box::new(ts.to()),
                ))),

                TEnv::TEnv1() => TEnv::TEnv0(Box::new(Inner::Inner1(
                    Box::new(x.clone()),
                    Box::new(COLON::new(":")),
                    Box::new(ts.to()),
                ))),
            },

            _TEnv::_TEnv1() => TEnv::TEnv1(),
        }
    }

    fn get_ftv(&self) -> HashSet<u32> {
        match self {
            _TEnv::_TEnv0(tenv, _, ts) => {
                let set1 = tenv.get_ftv();
                let set2 = ts.get_ftv();
                set1.union(&set2).map(|s| s.clone()).collect()
            }
            _TEnv::_TEnv1() => HashSet::new(),
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

fn eval_exp(tenv: &_TEnv, e: &Exp) -> io::Result<(Derivation, Capsule<_Type>)> {
    let (rule, _t) = match e {
        Exp::Exp0(le) => {
            let ret = eval_longexp(tenv, le);

            return ret;
        }
        Exp::Exp1(f) => {
            let ret = eval_fxp(tenv, f);

            return ret;
        }
        Exp::Exp2(g, _ /* < */, le) => {
            let (d0, t0) = eval_gxp(tenv, g)?;
            let (d1, t1) = eval_longexp(tenv, le)?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TLt(d0, d1), Capsule::make_bool())
        }
        Exp::Exp3(h, _ /* :: */, le) => {
            let (d0, t0) = eval_hxp(tenv, h)?;
            let (d1, t1) = eval_longexp(tenv, le)?;

            let () = _Type::merge(Capsule::make_list(t0), t1.clone())?;

            (Rule::TCons(d0, d1), t1)
        }
        Exp::Exp4(h, _ /* + */, le) => {
            let (d0, t0) = eval_hxp(tenv, h)?;
            let (d1, t1) = eval_longexp(tenv, le)?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TPlus(d0, d1), Capsule::make_int())
        }
        Exp::Exp5(h, _ /* - */, le) => {
            let (d0, t0) = eval_hxp(tenv, h)?;
            let (d1, t1) = eval_longexp(tenv, le)?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TMinus(d0, d1), Capsule::make_int())
        }
        Exp::Exp6(i, _ /* * */, le) => {
            let (d0, t0) = eval_ixp(tenv, i)?;

            let (d1, t1) = eval_longexp(tenv, le)?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TTimes(d0, d1), Capsule::make_int())
        }
    };

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(e.clone()),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((Derivation(j, Box::new(rule), _t.clone(), tenv.clone()), _t))
}

fn eval_longexp(tenv: &_TEnv, le: &LongExp) -> io::Result<(Derivation, Capsule<_Type>)> {
    let (rule, _t) = match le {
        LongExp::LongExp0(_, e0, _, e1, _, e2) => {
            let (d0, t0) = eval_exp(tenv, e0)?;
            let (d1, t1) = eval_exp(tenv, e1)?;
            let (d2, t2) = eval_exp(tenv, e2)?;

            let () = _Type::merge(t0, Capsule::make_bool())?;
            let () = _Type::merge(t1.clone(), t2)?;

            (Rule::TIf(d0, d1, d2), t1)
        }

        LongExp::LongExp1(_, x, _, e0, _, e1) => {
            let (d0, t0) = eval_exp(tenv, e0)?;
            let (d1, t1) = eval_exp(&tenv.push(x, _TyScheme::schemize(t0, tenv)), e1)?;

            (Rule::TLet(d0, d1), t1)
        }

        LongExp::LongExp2(_, x, _, e) => {
            let t0 = Capsule::make_dummy();
            let ts0 = _TyScheme(vec![], t0.clone());
            let (d0, t1) = eval_exp(&tenv.push(x, ts0), e)?;

            let _t = Capsule::make_func(t0, t1);

            (Rule::TAbs(d0), _t)
        }

        LongExp::LongExp3(_, _, x, _, _, y, _, e0, _, e1) => {
            let t0 = Capsule::make_dummy();
            let ts0 = _TyScheme(vec![], t0.clone());
            let t1 = Capsule::make_dummy();
            let t01 = Capsule::make_func(t0.clone(), t1.clone());
            let ts01 = _TyScheme(vec![], t01.clone());

            let (d0, t1_) = eval_exp(&tenv.push(x, ts01).push(y, ts0), e0)?;
            _Type::merge(t1.clone(), t1_)?;

            let (d1, _t) = eval_exp(&tenv.push(x, _TyScheme::schemize(t01, tenv)), e1)?;

            (Rule::TLetRec(d0, d1), _t)
        }

        LongExp::LongExp4(_, e0, _, _, _, _, e1, _, x, _, y, _, e2) => {
            let (d0, t0) = eval_exp(tenv, e0)?;
            let t_ = Capsule::make_dummy();
            _Type::merge(t0, Capsule::make_list(t_.clone()))?;
            let (d1, t1) = eval_exp(tenv, e1)?;

            let (d2, t2) = eval_exp(
                &tenv
                    .push(x, _TyScheme(vec![], t_.clone()))
                    .push(y, _TyScheme(vec![], Capsule::make_list(t_.clone()))),
                e2,
            )?;

            _Type::merge(t1, t2.clone())?;

            (Rule::TMatch(d0, d1, d2), t2)
        }
    };

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(le2e(le.clone())),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((Derivation(j, Box::new(rule), _t.clone(), tenv.clone()), _t))
}

fn eval_fxp(tenv: &_TEnv, f: &Fxp) -> io::Result<(Derivation, Capsule<_Type>)> {
    let (rule, _t) = match f {
        Fxp::Fxp0(g0, _ /* < */, g1) => {
            let (d0, t0) = eval_gxp(tenv, g0)?;
            let (d1, t1) = eval_gxp(tenv, g1)?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TLt(d0, d1), Capsule::make_bool())
        }

        Fxp::Fxp1(g) => {
            let ret = eval_gxp(tenv, g);

            return ret;
        }
    };

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(f.clone())),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((Derivation(j, Box::new(rule), _t.clone(), tenv.clone()), _t))
}

fn eval_gxp(tenv: &_TEnv, g: &Gxp) -> io::Result<(Derivation, Capsule<_Type>)> {
    let (rule, _t) = match g {
        Gxp::Gxp0(h, _ /* :: */, g) => {
            let (d0, t0) = eval_hxp(tenv, h)?;
            let (d1, t1) = eval_gxp(tenv, g)?;

            let () = _Type::merge(Capsule::make_list(t0), t1.clone())?;

            (Rule::TCons(d0, d1), t1)
        }

        Gxp::Gxp1(h) => {
            let ret = eval_hxp(tenv, h);

            return ret;
        }
    };

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(g.clone()))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((Derivation(j, Box::new(rule), _t.clone(), tenv.clone()), _t))
}

fn eval_hxp(tenv: &_TEnv, h: &Hxp) -> io::Result<(Derivation, Capsule<_Type>)> {
    let (rule, _t) = match h {
        Hxp::Hxp0(h, _ /* + */, i) => {
            let (d0, t0) = eval_hxp(tenv, h)?;
            let (d1, t1) = eval_ixp(tenv, i)?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TPlus(d0, d1), Capsule::make_int())
        }

        Hxp::Hxp1(h, _ /* - */, i) => {
            let (d0, t0) = eval_hxp(tenv, h)?;
            let (d1, t1) = eval_ixp(tenv, i)?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TMinus(d0, d1), Capsule::make_int())
        }

        Hxp::Hxp2(i) => {
            let ret = eval_ixp(tenv, i);

            return ret;
        }
    };

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(h.clone())))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((Derivation(j, Box::new(rule), _t.clone(), tenv.clone()), _t))
}

fn eval_ixp(tenv: &_TEnv, i: &Ixp) -> io::Result<(Derivation, Capsule<_Type>)> {
    let (rule, _t) = match i {
        Ixp::Ixp0(i, _ /* * */, j) => {
            let (d0, t0) = eval_ixp(tenv, i)?;
            let (d1, t1) = eval_jxp(tenv, j)?;

            let () = _Type::merge(t0, Capsule::make_int())?;
            let () = _Type::merge(t1, Capsule::make_int())?;

            (Rule::TTimes(d0, d1), Capsule::make_int())
        }

        Ixp::Ixp1(j) => {
            let ret = eval_jxp(tenv, j);

            return ret;
        }
    };

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(i.clone()))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((Derivation(j, Box::new(rule), _t.clone(), tenv.clone()), _t))
}

fn eval_jxp(tenv: &_TEnv, j: &Jxp) -> io::Result<(Derivation, Capsule<_Type>)> {
    let (rule, _t) = match j {
        Jxp::Jxp0(j0, k1) => {
            let (d0, t01) = eval_jxp(tenv, j0)?;
            let (d1, t0) = eval_kxp(tenv, k1)?;

            let t1 = Capsule::make_dummy();

            let () = _Type::merge(t01.clone(), Capsule::make_func(t0.clone(), t1.clone()))?;

            (Rule::TApp(d0, d1), t1)
        }

        Jxp::Jxp1(k) => {
            let ret = eval_kxp(tenv, k);

            return ret;
        }
    };

    let tmp_j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(j.clone())))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((
        Derivation(tmp_j, Box::new(rule), _t.clone(), tenv.clone()),
        _t,
    ))
}

fn eval_kxp(tenv: &_TEnv, k: &Kxp) -> io::Result<(Derivation, Capsule<_Type>)> {
    let (rule, _t) = match k {
        Kxp::Kxp0(n) => {
            let ret = eval_num(tenv, n);

            return ret;
        }
        Kxp::Kxp1(x) => {
            let ret = eval_truth(tenv, x);

            return ret;
        }
        Kxp::Kxp2(x) => {
            let ret = eval_var(tenv, x);

            return ret;
        }
        Kxp::Kxp3(_, _) => {
            let _t = Capsule::make_list(Capsule::make_dummy());

            (Rule::TNil, _t)
        }
        Kxp::Kxp4(_, e, _) => {
            let ret = eval_exp(tenv, e);

            return ret;
        }
    };

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(k2j(k.clone()))))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((Derivation(j, Box::new(rule), _t.clone(), tenv.clone()), _t))
}

fn eval_var(tenv: &_TEnv, x: &VAR) -> io::Result<(Derivation, Capsule<_Type>)> {
    fn find(tenv: &_TEnv, x: &VAR) -> io::Result<_TyScheme> {
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

    let (rule, ts) = (Rule::TVar, find(tenv, x)?);

    let _t = ts.instantiate();

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(k2j(Kxp::Kxp2(Box::new(x.clone()))))))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((Derivation(j, Box::new(rule), _t.clone(), tenv.clone()), _t))
}

fn eval_num(tenv: &_TEnv, n: &NUM) -> io::Result<(Derivation, Capsule<_Type>)> {
    let (rule, _t) = (Rule::TInt, Capsule::make_int());

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(k2j(Kxp::Kxp0(Box::new(n.clone()))))))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((Derivation(j, Box::new(rule), _t.clone(), tenv.clone()), _t))
}

fn eval_truth(tenv: &_TEnv, x: &TRUTH) -> io::Result<(Derivation, Capsule<_Type>)> {
    let (rule, _t) = (Rule::TBool, Capsule::make_bool());

    let j = Judgement::Judgement0(
        Box::new(TEnv::TEnv1()),
        Box::new(VDASH::new("|-")),
        Box::new(f2e(g2f(h2g(i2h(j2i(k2j(Kxp::Kxp1(Box::new(x.clone()))))))))),
        Box::new(COLON::new(":")),
        Box::new(Type::Type1(Box::new(EType::EType0(Box::new(INT::new(
            "dummy",
        )))))),
    );

    Ok((Derivation(j, Box::new(rule), _t.clone(), tenv.clone()), _t))
}

fn derive(j: &Judgement) -> io::Result<Derivation> {
    let Judgement::Judgement0(tenv, _, e, _, t) = j;

    let _t = Capsule::from(t);

    let _tenv = _TEnv::from(tenv);

    let (mut d, t_) = eval_exp(&_tenv, e)?;

    _Type::merge(_t, t_)?;

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
