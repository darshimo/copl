use ruly2::*;

syntax!(
    WHITESPACE {
        r"[ \n\r\t]*"
    }

    TOKEN {
        ARROW => {r"->"}
        NUM => {r"(0|(-)?[1-9][0-9]*)"}
        TRUTH => {r"(true|false)", Reserved}
        IF => {r"if", Reserved}
        THEN => {r"then", Reserved}
        ELSE => {r"else", Reserved}
        CROSS => {r"\+"}
        HYPHEN => {r"\-"}
        AST => {r"\*"}
        LT => {r"<"}
        PLUS => {r"plus", Reserved}
        MINUS => {r"minus", Reserved}
        TIMES => {r"times", Reserved}
        LESS => {r"less", Reserved}
        THAN => {r"than", Reserved}
        IS => {r"is", Reserved}
        EVALTO => {r"evalto", Reserved}
        LPAREN => {r"\("}
        RPAREN => {r"\)"}
        ERROR => {r"error", Reserved}
        COMMA => {r","}
        EQ => {r"="}
        VAR => {r"[a-z_][a-z_0-9']*"}
        VDASH => {r"\|-"}
        LET => {r"let", Reserved}
        IN => {r"in", Reserved}
        LBRACKET => {r"\["}
        RBRACKET => {r"\]"}
        FUN => {r"fun", Reserved}
        REC => {r"rec", Reserved}
    }

    RULE {
        Judgement =>
            | Judgement0(Env, VDASH, Exp, EVALTO, Value)
            | Judgement1(NUM, PLUS, NUM, IS, NUM)
            | Judgement2(NUM, MINUS, NUM, IS, NUM)
            | Judgement3(NUM, TIMES, NUM, IS, NUM)
            | Judgement4(NUM, LESS, THAN, NUM, IS, TRUTH)

        Env =>
            | Env0(EnvList)
            | Env1()

        EnvList =>
            | EnvList0(EnvList, COMMA, VAR, EQ, Value)
            | EnvList1(VAR, EQ, Value)

        Value =>
            | Value0(NUM)
            | Value1(TRUTH)
            | Value2(LPAREN, Env, RPAREN, LBRACKET, FUN, VAR, ARROW, Exp, RBRACKET)
            | Value3(LPAREN, Env, RPAREN, LBRACKET, REC, VAR, EQ, FUN, VAR, ARROW, Exp, RBRACKET)

        Exp =>
            | Exp0(LongExp)
            | Exp1(Fxp)

        LongExp =>
            | LongExp0(IF, Exp, THEN, Exp, ELSE, Exp)
            | LongExp1(LET, VAR, EQ, Exp, IN, Exp)
            | LongExp2(FUN, VAR, ARROW, Exp)
            | LongExp3(LET, REC, VAR, EQ, FUN, VAR, ARROW, Exp, IN, Exp)

        // <以下
        Fxp =>
            | Fxp0(Gxp, LT, LongExp)
            | Fxp1(Gxp, LT, Gxp)
            | Fxp2(Gxp)

        // +/-以下
        Gxp =>
            | Gxp0(Gxp, CROSS, LongExp)
            | Gxp1(Gxp, HYPHEN, LongExp)
            | Gxp2(Gxp, CROSS, Hxp)
            | Gxp3(Gxp, HYPHEN, Hxp)
            | Gxp4(Hxp)

        // *以下
        Hxp =>
            | Hxp0(Hxp, AST, LongExp)
            | Hxp1(Hxp, AST, Ixp)
            | Hxp2(Ixp)

        Ixp =>
            | Ixp0(Ixp, Jxp)
            | Ixp1(Jxp)

        Jxp =>
            | Jxp0(NUM)
            | Jxp1(TRUTH)
            | Jxp2(VAR)
            | Jxp3(LPAREN, Exp, RPAREN)
    }

    START {
        Judgement
    }

    ALGORITHM {
        LR1
    }
);
