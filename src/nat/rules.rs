use crate::tmp::reg;
use ruly::{Parse, Product};

add_rule!(
    Nat => Zero ({reg("Z")})
        |   Succ ({reg("S")},{reg(r"\(")},Nat,{reg(r"\)")})
);

add_rule!(
    Judgement => Plus (Nat, {reg("plus")}, Nat, {reg("is")}, Nat)
        |   Times (Nat, {reg("times")}, Nat, {reg("is")}, Nat)
);
