use crate::tmp::reg;
use ruly::*;

add_rule!(
    Nat => Zero ({reg("Z")})
        |   Succ ({reg("S")},{reg(r"\(")},Nat,{reg(r"\)")})
);

add_rule!(
    Judgement => Eval (Exp, {reg("evalto")}, Nat)
        |   Plus (Nat, {reg("plus")}, Nat, {reg("is")}, Nat)
        |   Times (Nat, {reg("times")}, Nat, {reg("is")}, Nat)
);

add_rule!(
    Exp => Exp0 (Fxp, {reg(r"\+")}, Exp)
        |   Exp1 (Fxp)
        |   ExpDummy2 (Exp, {reg(r"\+")}, Fxp)
);

add_rule!(
    Fxp => Fxp0 (Gxp, {reg(r"\*")}, Fxp)
        |   Fxp1 (Gxp)
        |   FxpDummy2 (Fxp, {reg(r"\*")}, Gxp)
);

add_rule!(
    Gxp => Gxp0 ({reg(r"\(")}, Exp, {reg(r"\)")})
        |   Gxp1 (Nat)
);
