use ruly2::*;

syntax!(
    WHITESPACE {
        r"[ \n\r\t]*"
    }

    TOKEN {
        NUM => {r"(0|(-)?[1-9][0-9]*)"}
        TRUTH => {r"(true|false)"}
        IF => {r"if"}
        THEN => {r"then"}
        ELSE => {r"else"}
        CROSS => {r"\+"}
        HYPHEN => {r"\-"}
        AST => {r"\*"}
        LT => {r"<"}
        PLUS => {r"plus"}
        MINUS => {r"minus"}
        TIMES => {r"times"}
        LESS => {r"less"}
        THAN => {r"than"}
        IS => {r"is"}
        EVALTO => {r"evalto"}
        LPAREN => {r"\("}
        RPAREN => {r"\)"}
        EPASS => {r">>"}
        VPASS => {r"=>"}
        UNDERLINE => {r"_"}
        LBRACE => {r"\{"}
        RBRACE => {r"\}"}
    }

    RULE {
        Judgement =>
            | Judgement0(Value, VPASS, Cont, EVALTO, Value)
            | Judgement1(Exp, EPASS, Cont, EVALTO, Value)
            | Judgement2(Exp, EVALTO, Value)
            | Judgement3(NUM, PLUS, NUM, IS, NUM)
            | Judgement4(NUM, MINUS, NUM, IS, NUM)
            | Judgement5(NUM, TIMES, NUM, IS, NUM)
            | Judgement6(NUM, LESS, THAN, NUM, IS, TRUTH)

        Value =>
            | Value0(NUM)
            | Value1(TRUTH)

        Exp =>
            | Exp0(LongExp)
            | Exp1(Fxp)
            | Exp2(Gxp, LT, LongExp)
            | Exp3(Gxp, CROSS, LongExp)
            | Exp4(Gxp, HYPHEN, LongExp)
            | Exp5(Hxp, AST, LongExp)

        LongExp =>
            | LongExp0(IF, Exp, THEN, Exp, ELSE, Exp)

        Fxp =>
            | Fxp0(Gxp, LT, Gxp)
            | Fxp1(Gxp)

        Gxp =>
            | Gxp0(Gxp, CROSS, Hxp)
            | Gxp1(Gxp, HYPHEN, Hxp)
            | Gxp2(Hxp)

        Hxp =>
            | Hxp0(Hxp, AST, Ixp)
            | Hxp1(Ixp)

        Ixp =>
            | Ixp0(NUM)
            | Ixp1(TRUTH)
            | Ixp2(LPAREN, Exp, RPAREN)

        Op =>
            | Op0(LT)
            | Op1(CROSS)
            | Op2(HYPHEN)
            | Op3(AST)

        Cont =>
            | Cont0(ContElem, EPASS, Cont)
            | Cont1(FinalContElem)

        ContElem =>
            | ContElem0(LBRACE, UNDERLINE, Op, Exp, RBRACE)
            | ContElem1(LBRACE, Value, Op, UNDERLINE, RBRACE)
            | ContElem2(LBRACE, IF, UNDERLINE, THEN, Exp, ELSE, Exp, RBRACE)

        FinalContElem =>
            | FinalContElem0(UNDERLINE)
            | FinalContElem1(ContElem)
    }

    START {
        Judgement
    }

    ALGORITHM {
        LR1
    }
);
