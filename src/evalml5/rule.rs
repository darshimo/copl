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
        CONS => {r"::"}
        MATCH => {r"match", Reserved}
        WITH => {r"with", Reserved}
        BAR => {r"\|"}
        UNDERLINE => {r"_", Reserved}
        MATCHES => {r"matches", Reserved}
        WHEN => {r"when", Reserved}
        DOESNT => {r"doesn't",Reserved}
    }

    RULE {
        Judgement =>
            | Judgement0(Env, VDASH, Exp, EVALTO, Value)
            | Judgement1(NUM, PLUS, NUM, IS, NUM)
            | Judgement2(NUM, MINUS, NUM, IS, NUM)
            | Judgement3(NUM, TIMES, NUM, IS, NUM)
            | Judgement4(NUM, LESS, THAN, NUM, IS, TRUTH)
            | Judgement5(Pat, MATCHES, Value, WHEN, LPAREN, Env, RPAREN)
            | Judgement6(Pat, DOESNT, MATCH, Value)

        Env =>
            | Env0(EnvList)
            | Env1()

        EnvList =>
            | EnvList0(EnvList, COMMA, VAR, EQ, Value)
            | EnvList1(VAR, EQ, Value)

        Value =>
            | Value0(Element, CONS, Value)
            | Value1(Element)

        Element =>
            | Element0(NUM)
            | Element1(TRUTH)
            | Element2(LPAREN, Env, RPAREN, LBRACKET, FUN, VAR, ARROW, Exp, RBRACKET)
            | Element3(LPAREN, Env, RPAREN, LBRACKET, REC, VAR, EQ, FUN, VAR, ARROW, Exp, RBRACKET)
            | Element4(LBRACKET, RBRACKET)
            | Element5(LPAREN, Value, RPAREN)

        Pat =>
            | Pat0(SubPat, CONS, Pat)
            | Pat1(SubPat)

        SubPat =>
            | SubPat0(VAR)
            | SubPat1(LBRACKET, RBRACKET)
            | SubPat2(UNDERLINE)
            | SubPat3(LPAREN, Pat, RPAREN)

        Clauses =>
            | Clauses0(Pat, ARROW, Exp, BAR, Clauses)
            | Clauses1(Pat, ARROW, Exp)

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
            | LongExp4(MATCH, Exp, WITH, Clauses)

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
