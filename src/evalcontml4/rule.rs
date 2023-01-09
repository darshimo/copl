use ruly2::*;

syntax!(
    WHITESPACE {
        r"[ \n\r\t]*"
    }

    TOKEN {
        EPASS => {r">>"}
        VPASS => {r"=>"}
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
        LBRACE => {r"\{"}
        RBRACE => {r"\}"}
        LETCC => {r"letcc", Reserved}
    }

    RULE {
        Judgement =>
            | Judgement0(Value, VPASS, Cont, EVALTO, Value)
            | Judgement1(Env, VDASH, Exp, EPASS, Cont, EVALTO, Value)
            | Judgement2(Env, VDASH, Exp, EVALTO, Value)
            | Judgement3(NUM, PLUS, NUM, IS, NUM)
            | Judgement4(NUM, MINUS, NUM, IS, NUM)
            | Judgement5(NUM, TIMES, NUM, IS, NUM)
            | Judgement6(NUM, LESS, THAN, NUM, IS, TRUTH)

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
            | Element5(LBRACKET, Cont, RBRACKET)
            | Element6(LPAREN, Value, RPAREN)

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
            | LongExp5(LETCC, VAR, IN, Exp)

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

        Op =>
            | Op0(LT)
            | Op1(CROSS)
            | Op2(HYPHEN)
            | Op3(AST)

        Cont =>
            | Cont0(ContElem, EPASS, Cont)
            | Cont1(FinalContElem)

        ContElem =>
            | ContElem0(LBRACE, Env, VDASH, UNDERLINE, Op, Exp, RBRACE)
            | ContElem1(LBRACE, Value, Op, UNDERLINE, RBRACE)
            | ContElem2(LBRACE, Env, VDASH, IF, UNDERLINE, THEN, Exp, ELSE, Exp, RBRACE)
            | ContElem3(LBRACE, Env, VDASH, LET, VAR, EQ, UNDERLINE, IN, Exp, RBRACE)
            | ContElem4(LBRACE, Env, VDASH, UNDERLINE, Exp, RBRACE)
            | ContElem5(LBRACE, Value, UNDERLINE, RBRACE)
            | ContElem6(LBRACE, Env, VDASH, UNDERLINE, CONS, Exp, RBRACE)
            | ContElem7(LBRACE, Element, CONS, UNDERLINE, RBRACE)
            | ContElem8(LBRACE, Env, VDASH, MATCH, UNDERLINE, WITH, LBRACKET, RBRACKET, ARROW, Exp, BAR, VAR, CONS, VAR, ARROW, Exp, RBRACE)

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
