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
        TRANS => {r"==>"}
        LPAREN => {r"\("}
        RPAREN => {r"\)"}
        COMMA => {r","}
        EQ => {r"="}
        VAR => {r"[a-z_][a-z_0-9']*"}
        VDASH => {r"\|-"}
        LET => {r"let", Reserved}
        IN => {r"in", Reserved}
        FUN => {r"fun", Reserved}
        REC => {r"rec", Reserved}
        PERIOD => {r"\."}
        DBVAR => {r"#[1-9][0-9]*"}
    }

    RULE {
        Judgement =>
            | Judgement0(VarList, VDASH, Exp, TRANS, DBExp)

        VarList =>
            | VarList0(Inner)
            | VarList1()

        Inner =>
            | Inner0(Inner, COMMA, VAR)
            | Inner1(VAR)

        Exp =>
            | Exp0(LongExp)
            | Exp1(Fxp)
            | Exp2(Gxp, LT, LongExp)
            | Exp3(Gxp, CROSS, LongExp)
            | Exp4(Gxp, HYPHEN, LongExp)
            | Exp5(Hxp, AST, LongExp)

        LongExp =>
            | LongExp0(IF, Exp, THEN, Exp, ELSE, Exp)
            | LongExp1(LET, VAR, EQ, Exp, IN, Exp)
            | LongExp2(FUN, VAR, ARROW, Exp)
            | LongExp3(LET, REC, VAR, EQ, FUN, VAR, ARROW, Exp, IN, Exp)

        // <以下
        Fxp =>
            | Fxp0(Gxp, LT, Gxp)
            | Fxp1(Gxp)

        // +/-以下
        Gxp =>
            | Gxp0(Gxp, CROSS, Hxp)
            | Gxp1(Gxp, HYPHEN, Hxp)
            | Gxp2(Hxp)

        // *以下
        Hxp =>
            | Hxp0(Hxp, AST, Ixp)
            | Hxp1(Ixp)

        Ixp =>
            | Ixp0(Ixp, Jxp)
            | Ixp1(Jxp)

        Jxp =>
            | Jxp0(NUM)
            | Jxp1(TRUTH)
            | Jxp2(VAR)
            | Jxp3(LPAREN, Exp, RPAREN)

        DBExp =>
            | DBExp0(DBLongExp)
            | DBExp1(DBFxp)
            | DBExp2(DBGxp, LT, DBLongExp)
            | DBExp3(DBGxp, CROSS, DBLongExp)
            | DBExp4(DBGxp, HYPHEN, DBLongExp)
            | DBExp5(DBHxp, AST, DBLongExp)

        DBLongExp =>
            | DBLongExp0(IF, DBExp, THEN, DBExp, ELSE, DBExp)
            | DBLongExp1(LET, PERIOD, EQ, DBExp, IN, DBExp)
            | DBLongExp2(FUN, PERIOD, ARROW, DBExp)
            | DBLongExp3(LET, REC, PERIOD, EQ, FUN, PERIOD, ARROW, DBExp, IN, DBExp)

        // <以下
        DBFxp =>
            | DBFxp0(DBGxp, LT, DBGxp)
            | DBFxp1(DBGxp)

        // +/-以下
        DBGxp =>
            | DBGxp0(DBGxp, CROSS, DBHxp)
            | DBGxp1(DBGxp, HYPHEN, DBHxp)
            | DBGxp2(DBHxp)

        // *以下
        DBHxp =>
            | DBHxp0(DBHxp, AST, DBIxp)
            | DBHxp1(DBIxp)

        DBIxp =>
            | DBIxp0(DBIxp, DBJxp)
            | DBIxp1(DBJxp)

        DBJxp =>
            | DBJxp0(NUM)
            | DBJxp1(TRUTH)
            | DBJxp2(DBVAR)
            | DBJxp3(LPAREN, DBExp, RPAREN)
    }

    START {
        Judgement
    }

    ALGORITHM {
        LR1
    }
);
