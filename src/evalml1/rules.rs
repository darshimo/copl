use crate::tmp::reg;
use ruly::*;

add_rule!(
    Int => Int0 ({reg(r"(0|(-)?[1-9][0-9]*)"), i32, |s: String|s.parse::<i32>().unwrap()})
);

add_rule!(
    Bool => Bool0 ({reg(r"(true|false)"), bool, |s: String|s=="true"})
);

add_rule!(
    Value => Value0 (Int)
        |   Value1 (Bool)
);

add_rule!(
    Exp => Exp0 (Fxp, {reg("<")}, Exp)
        |   Exp1 (Fxp)
);

add_rule!(
    Fxp => Fxp0 (Gxp, {reg(r"\+|\-")}, Fxp)
        |   Fxp1 (Gxp)
        |   FxpDummy2 (Fxp, {reg(r"\+|\-")}, Gxp)
);

add_rule!(
    Gxp => Gxp0 (Hxp, {reg(r"\*")}, Gxp)
        |   Gxp1 (Hxp)
        |   GxpDummy2 (Gxp, {reg(r"\*")}, Hxp)
);

add_rule!(
    Hxp => Hxp0 ({reg("if")}, Exp, {reg("then")}, Exp, {reg("else")}, Exp)
        |   Hxp1 ({reg(r"\(")}, Exp, {reg(r"\)")})
        |   Hxp2 (Int)
        |   Hxp3 (Bool)
);

add_rule!(
    Judgement => Eval (Exp, {reg("evalto")}, Value)
        |   Plus (Int, {reg("plus")}, Int, {reg("is")}, Int)
        |   Minus (Int, {reg("minus")}, Int, {reg("is")}, Int)
        |   Times (Int, {reg("times")}, Int, {reg("is")}, Int)
        |   Lt (Int, {reg("less")}, {reg("than")}, Int, {reg("is")}, Bool)
);
