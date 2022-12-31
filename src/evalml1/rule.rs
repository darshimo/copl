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
        ERROR => {r"error"}
    }

    RULE {
        Judgement =>
            | Judgement0(Exp, EVALTO, Res)
            | Judgement1(NUM, PLUS, NUM, IS, NUM)
            | Judgement2(NUM, MINUS, NUM, IS, NUM)
            | Judgement3(NUM, TIMES, NUM, IS, NUM)
            | Judgement4(NUM, LESS, THAN, NUM, IS, TRUTH)

        Value =>
            | Value0(NUM)
            | Value1(TRUTH)

        Res =>
            | Res0(Value)
            | Res1(ERROR)

        Exp =>
            | Exp0(IfExp)
            | Exp1(Fxp)

        IfExp =>
            | IfExp0(IF, Exp, THEN, Exp, ELSE, Exp)

        Fxp =>
            | Fxp0(Gxp, LT, IfExp)
            | Fxp1(Gxp, LT, Gxp)
            | Fxp2(Gxp)

        Gxp =>
            | Gxp0(Gxp, CROSS, IfExp)
            | Gxp1(Gxp, HYPHEN, IfExp)
            | Gxp2(Gxp, CROSS, Hxp)
            | Gxp3(Gxp, HYPHEN, Hxp)
            | Gxp4(Hxp)

        Hxp =>
            | Hxp0(Hxp, AST, IfExp)
            | Hxp1(Hxp, AST, Ixp)
            | Hxp2(Ixp)

        Ixp =>
            | Ixp0(NUM)
            | Ixp1(TRUTH)
            | Ixp2(LPAREN, Exp, RPAREN)
    }

    START {
        Judgement
    }

    ALGORITHM {
        LR1
    }
);
