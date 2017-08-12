#include "aldor"
#include "aldorio"
#pile

import from SpadTypeLib
inline from SpadTypeLib

SExpressionOutputType: Category == OutputType with
    sexpression: % -> SExpression
    default
        import from SExpression
        (o: TextWriter) << (obj: %): TextWriter == o << sexpression obj

SExpressionInputType: Category == InputType with
    parseSExpression: SExpression -> %
    default
        import from SExpressionReader, Partial SExpression
        << (ins: TextReader): % == parseSExpression retract read ins

BaseAbSynCategory: Category == Extensible with
    PrimitiveType
    newApply: (%, List %) -> %
    newNone: () -> %

    apply?: % -> Boolean
    applyOperator: % -> %
    applyArguments: % -> List %

    id?: % -> Boolean

    literal?: % -> Boolean
    newLiteral: String -> %
    literal: % -> String

    none?: % -> Boolean


AbSynCategory(T: PrimitiveType): Category == BaseAbSynCategory with
    idSymbol: % -> T
    newId: T -> %
    if T has SExpressionOutputType then SExpressionOutputType

AbSynAny(T: PrimitiveType): AbSynCategory(T) with
== add
    Application == Record(op: %, args: List %)
    Lit == String
    Struct == Union(id: T, app: Application, lit: Lit, none: Cross())
    Rep == Record(fields: Fields %, struct: Struct)
    import from Rep, Application, Fields %

    newId(s: T): % == per [newFields(), [s]]
    newApply(op: %, args: List %): % == per [newFields(), [[op, args]]]
    newNone(): % == per [newFields(), [()@Cross()]]

    apply?(ab: %): Boolean == rep(ab).struct case app
    applyOperator(ab: %): % == rep(ab).struct.app.op
    applyArguments(ab: %): List % == rep(ab).struct.app.args

    id?(ab: %): Boolean == rep(ab).struct case id -- rep(ab) case id
    idSymbol(ab: %): T == rep(ab).struct.id -- rep(ab).id

    newLiteral(s: String): % == per [newFields(), [s]]
    literal?(ab: %): Boolean == rep(ab).struct case lit
    literal(ab: %): String == rep(ab).struct.lit

    none?(ab: %): Boolean == rep(ab).struct case none

    fields(ab: %): Fields % == rep(ab).fields

    (ab1: %) = (ab2: %): Boolean ==
        id? ab1 => id? ab2 and idSymbol ab1 = idSymbol ab2
        apply? ab1 => apply? ab2
                        and rep(ab1).struct.app.op = rep(ab1).struct.app.op
                        and rep(ab1).struct.app.args = rep(ab1).struct.app.args
        error("Odd AbSyn for equality")

    if T has SExpressionOutputType then
        sexpression(ab: %): SExpression ==
            import from List %
            id? ab => sexpression idSymbol ab
            apply? ab => cons(sexpression applyOperator ab, [sexpression arg for arg in applyArguments ab])
            none? ab => nil
            literal? ab => sexpr literal ab
            error("odd absyn")

AbSyn: AbSynCategory Symbol with
    SExpressionInputType
    SExpressionOutputType
== AbSynAny(Symbol) add

    sexpression(ab: %): SExpression ==
        import from List %
        id? ab => sexpr idSymbol ab
        apply? ab => cons(sexpression applyOperator ab, [sexpression arg for arg in applyArguments ab])
        none? ab => nil
        literal? ab => sexpr literal ab
        error("odd absyn")

    parseSExpression(sx: SExpression): % == parse(sx)$AbSynParser

AbSynParser: with
    parse: SExpression -> AbSyn
== add
    parse(sx: SExpression): AbSyn ==
        if cons? sx then parseCons(sx) else parseId(sx)

    local parseCons(sx: SExpression): AbSyn ==
        import from List AbSyn
        op: AbSyn := parse(first sx)
        args := [parse elt for elt in rest sx]
        newApply(op, args)

    local parseId(sx: SExpression): AbSyn ==
        sym? sx => newId sym sx
        str? sx => newLiteral str sx
        error("Parsing " + (toString sx))

AbSynUtils: with
    principalOperator: AbSyn -> Symbol
== add
    principalOperator(ab: AbSyn): Symbol ==
        apply? ab => principalOperator applyOperator ab
        id? ab => idSymbol ab
        never
