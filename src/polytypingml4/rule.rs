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
        LPAREN => {r"\("}
        RPAREN => {r"\)"}
        COMMA => {r","}
        PERIOD =>{r"\."}
        EQ => {r"="}
        VAR => {r"[a-z_][a-z_0-9']*"}
        VDASH => {r"\|-"}
        LET => {r"let", Reserved}
        IN => {r"in", Reserved}
        LBRACKET => {r"\["}
        RBRACKET => {r"\]"}
        FUN => {r"fun", Reserved}
        REC => {r"rec", Reserved}
        CONS => {r"::"}
        MATCH => {r"match", Reserved}
        WITH => {r"with", Reserved}
        BAR => {r"\|"}
        COLON => {r":"}
        BOOL => {r"bool", Reserved}
        INT => {r"int", Reserved}
        LIST => {r"list", Reserved}
        TVAR => {r"'[a-z][a-z_0-9]*"}
    }

    RULE {
        Judgement =>
            | Judgement0(TEnv, VDASH, Exp, COLON, Type)

        TEnv =>
            | TEnv0(Inner)
            | TEnv1()

        Inner =>
            | Inner0(Inner, COMMA, VAR, COLON, TyScheme)
            | Inner1(VAR, COLON, TyScheme)

        Type =>
            | Type0(EType, ARROW, Type)
            | Type1(EType)

        EType =>
            | EType0(INT)
            | EType1(BOOL)
            | EType2(EType, LIST)
            | EType3(LPAREN, Type, RPAREN)
            | EType4(TVAR)

        TyScheme =>
            | TyScheme0(TVarList, PERIOD, Type)
            | TyScheme1(Type)

        TVarList =>
            | TVarList0(TVarList, TVAR)
            | TVarList1(TVAR)

        Exp =>
            | Exp0(LongExp)
            | Exp1(Fxp)
            | Exp2(Gxp, LT, LongExp)
            | Exp3(Hxp, CONS, LongExp)
            | Exp4(Hxp, CROSS, LongExp)
            | Exp5(Hxp, HYPHEN, LongExp)
            | Exp6(Ixp, AST, LongExp)

        LongExp =>
            | LongExp0(IF, Exp, THEN, Exp, ELSE, Exp)
            | LongExp1(LET, VAR, EQ, Exp, IN, Exp)
            | LongExp2(FUN, VAR, ARROW, Exp)
            | LongExp3(LET, REC, VAR, EQ, FUN, VAR, ARROW, Exp, IN, Exp)
            | LongExp4(MATCH, Exp, WITH, LBRACKET, RBRACKET, ARROW, Exp, BAR, VAR, CONS, VAR, ARROW, Exp)

        // <以下
        Fxp =>
            | Fxp0(Gxp, LT, Gxp)
            | Fxp1(Gxp)

        // ::
        Gxp =>
            | Gxp0(Hxp, CONS, Gxp)
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
            | Kxp3(LBRACKET, RBRACKET)
            | Kxp4(LPAREN, Exp, RPAREN)
    }

    START {
        Judgement
    }

    ALGORITHM {
        LR1
    }
);
