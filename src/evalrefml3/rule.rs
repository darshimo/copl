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
        DEREF => {r"!"}
        LOC => {r"@[a-z_][a-z_0-9']*"}
        SLASH => {r"/"}
        REF => {r"ref", Reserved}
        ASSIGN => {r":="}
    }

    RULE {
        Judgement =>
            | Judgement0(PreStore, Env, VDASH, Exp, EVALTO, Value, PostStore)
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

        PreStore =>
            | PreStore0(LocList, SLASH)
            | PreStore1()

        PostStore =>
            | PostStore0(SLASH, LocList)
            | PostStore1()

        LocList =>
            | LocList0(LocList, COMMA, LOC, EQ, Value)
            | LocList1(LOC, EQ, Value)

        Value =>
            | Value0(NUM)
            | Value1(TRUTH)
            | Value2(LPAREN, Env, RPAREN, LBRACKET, FUN, VAR, ARROW, Exp, RBRACKET)
            | Value3(LPAREN, Env, RPAREN, LBRACKET, REC, VAR, EQ, FUN, VAR, ARROW, Exp, RBRACKET)
            | Value4(LOC)

        Exp =>
            | Exp0(LongExp)
            | Exp1(Fxp)
            | Exp2(Hxp, LT, LongExp)
            | Exp3(Hxp, CROSS, LongExp)
            | Exp4(Hxp, HYPHEN, LongExp)
            | Exp5(Ixp, AST, LongExp)

        LongExp =>
            | LongExp0(IF, Exp, THEN, Exp, ELSE, Exp)
            | LongExp1(LET, VAR, EQ, Exp, IN, Exp)
            | LongExp2(FUN, VAR, ARROW, Exp)
            | LongExp3(LET, REC, VAR, EQ, FUN, VAR, ARROW, Exp, IN, Exp)

        Fxp =>
            | Fxp0(Gxp, ASSIGN, Fxp)
            | Fxp1(Gxp)

        // <以下
        Gxp =>
            | Gxp0(Hxp, LT, Hxp)
            | Gxp1(Hxp)

        // +/-以下
        Hxp =>
            | Hxp0(Hxp, CROSS, Ixp)
            | Hxp1(Hxp, HYPHEN, Ixp)
            | Hxp2(Ixp)

        // *以下
        Ixp =>
            | Ixp0(Ixp, AST, Jxp)
            | Ixp1(Jxp)

        Jxp =>
            | Jxp0(Jxp, Kxp)
            | Jxp1(Kxp)

        Kxp =>
            | Kxp0(NUM)
            | Kxp1(TRUTH)
            | Kxp2(VAR)
            | Kxp3(REF, Kxp)
            | Kxp4(DEREF, Kxp)
            | Kxp5(LPAREN, Exp, RPAREN)
    }

    START {
        Judgement
    }

    ALGORITHM {
        LR1
    }
);
