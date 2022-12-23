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
        Is => {"is"}
        Less => {"less"}
        Than => {"than"}
    }

    RULE {
        Judgement =>
            | Judgement0(Nat, Is, Less, Than, Nat)

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
