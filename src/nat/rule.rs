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
    }

    RULE {
        Judgement =>
            | Judgement0(Nat, Plus, Nat, Is, Nat)
            | Judgement1(Nat, Times, Nat, Is, Nat)

        Nat =>
            | Nat0(Succ, Lparen, Nat, Rparen)
            | Nat1(Zero)
    }

    START {
        Judgement
    }

    ALGORITHM {
        LR0
    }
);
