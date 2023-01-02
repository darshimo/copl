use ruly2::*;

syntax!(
    WHITESPACE {
        r"[ \n\r\t]*"
    }

    TOKEN {
        ARROW => {r"->"}
        NUM => {r"(0|(-)?[1-9][0-9]*)"}
        TRUTH => {r"(true|false)"}
        IF => {r"if"}
        THEN => {r"then"}
        ELSE => {r"else"}
        CROSS => {r"\+"}
        HYPHEN => {r"\-"}
        AST => {r"\*"}
        LT => {r"<"}
        EVALTO => {r"evalto"}
        LPAREN => {r"\("}
        RPAREN => {r"\)"}
        COMMA => {r","}
        EQ => {r"="}
        VDASH => {r"\|-"}
        LET => {r"let"}
        IN => {r"in"}
        FUN => {r"fun"}
        REC => {r"rec"}
        PERIOD => {r"\."}
        DBVAR => {r"#[1-9][0-9]*"}
        LBRACKET => {r"\["}
        RBRACKET => {r"\]"}
        PLUS => {r"plus"}
        MINUS => {r"minus"}
        TIMES => {r"times"}
        LESS => {r"less"}
        THAN => {r"than"}
        IS => {r"is"}
    }

    RULE {
        Judgement =>
            | Judgement0(DBValueList, VDASH, DBExp, EVALTO, DBValue)
            | Judgement1(NUM, PLUS, NUM, IS, NUM)
            | Judgement2(NUM, MINUS, NUM, IS, NUM)
            | Judgement3(NUM, TIMES, NUM, IS, NUM)
            | Judgement4(NUM, LESS, THAN, NUM, IS, TRUTH)

        DBValueList =>
            | DBValueList0(Inner)
            | DBValueList1()

        Inner =>
            | Inner0(Inner, COMMA, DBValue)
            | Inner1(DBValue)

        DBValue =>
            | DBValue0(NUM)
            | DBValue1(TRUTH)
            | DBValue2(LPAREN, DBValueList, RPAREN, LBRACKET, FUN, PERIOD, ARROW, DBExp, RBRACKET)
            | DBValue3(LPAREN, DBValueList, RPAREN, LBRACKET, REC, PERIOD, EQ, FUN, PERIOD, ARROW, DBExp, RBRACKET)

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
