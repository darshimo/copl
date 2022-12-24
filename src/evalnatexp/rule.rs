use ruly2::*;

syntax!(
    WHITESPACE {
        r"[ \n\r\t]*"
    }

    TOKEN {
        Zero => {"Z"}
        Succ => {"S"}
        Lparen => {r"\("}
        Rparen => {r"\)"}
        Plus => {"plus"}
        Times => {"times"}
        Is => {"is"}
        P => {r"\+"}
        M => {r"\*"}
        Evalto => {"evalto"}
    }

    RULE {
        Judgement =>
            | Judgement0(Exp, Evalto, Nat)
            | Judgement1(Nat, Plus, Nat, Is, Nat)
            | Judgement2(Nat, Times, Nat, Is, Nat)

        Nat =>
            | Nat0(Succ, Lparen, Nat, Rparen)
            | Nat1(Zero)

        Exp =>
            | Exp0(Exp, P, Fxp)
            | Exp1(Fxp)

        Fxp =>
            | Fxp0(Fxp, M, Gxp)
            | Fxp1(Gxp)

        Gxp =>
            | Gxp0(Lparen, Exp, Rparen)
            | Gxp1(Nat)
    }

    START {
        Judgement
    }

    ALGORITHM {
        SLR
    }
);
