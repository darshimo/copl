use ruly2::*;

syntax!(
    WHITESPACE {
        r"[ \n\r\t]*"
    }

    TOKEN {
        NUM => {r"(0|(-)?[1-9][0-9]*)"}
        TRUTH => {r"(true|false)", Reserved}
        VAR => {r"[a-z_][a-z_0-9']*"}
        CROSS => {r"\+"}
        HYPHEN => {r"\-"}
        AST => {r"\*"}
        NOT => {r"!"}
        AND => {r"&&"}
        OR => {r"\|\|"}
        LT => {r"<"}
        EQ => {r"="}
        LE => {r"<="}
        SKIP => {r"skip", Reserved}
        ASSIGN => {r":="}
        SEMICOLON => {r";"}
        IF => {r"if", Reserved}
        THEN => {r"then", Reserved}
        ELSE => {r"else", Reserved}
        WHILE => {r"while", Reserved}
        LPAREN => {r"\("}
        RPAREN => {r"\)"}
        DO => {r"do", Reserved}
        COMMA => {r","}
        VDASH => {r"\|-"}
        EVALTO => {r"evalto", Reserved}
        CHANGES => {r"changes", Reserved}
        TO => {r"to", Reserved}
    }

    RULE {
        Judgement =>
            | Judgement0(Store, VDASH, AExp, EVALTO, NUM)
            | Judgement1(Store, VDASH, BExp, EVALTO, TRUTH)
            | Judgement2(Coms, CHANGES, Store, TO, Store)

        Store =>
            | Store0(Inner)
            | Store1()

        Inner =>
            | Inner0(Inner, COMMA, VAR, EQ, NUM)
            | Inner1(VAR, EQ, NUM)

        AExp =>
            | AExp0(AExp, CROSS, AFxp)
            | AExp1(AExp, HYPHEN, AFxp)
            | AExp2(AFxp)

        AFxp =>
            | AFxp0(AFxp, AST, AGxp)
            | AFxp1(AGxp)

        AGxp =>
            | AGxp0(NUM)
            | AGxp1(VAR)
            | AGxp2(LPAREN, AExp, RPAREN)

        BExp =>
            | BExp0(BExp, OR, BFxp)
            | BExp1(BFxp)

        BFxp =>
            | BFxp0(BFxp, AND, BGxp)
            | BFxp1(BGxp)

        BGxp =>
            | BGxp0(AExp, Comp, AExp)
            | BGxp1(BHxp)

        BHxp =>
            | BHxp0(NOT, BHxp)
            | BHxp1(TRUTH)
            | BHxp2(LPAREN, BExp, RPAREN)

        Comp =>
            | Comp0(LT)
            | Comp1(EQ)
            | Comp2(LE)

        Coms =>
            | Coms0(Com, SEMICOLON, Coms)
            | Coms1(Com)

        Com =>
            | Com0(SKIP)
            | Com1(VAR, ASSIGN, AExp)
            | Com2(IF, BExp, THEN, Coms, ELSE, Coms)
            | Com3(WHILE, LPAREN, BExp, RPAREN, DO, Coms)
            | Com4(LPAREN, Coms, RPAREN)
    }

    START {
        Judgement
    }

    ALGORITHM {
        LR1
    }
);
