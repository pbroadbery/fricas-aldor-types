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

    apply?: % -> Boolean
    newApply: (%, List %) -> %
    applyOperator: % -> %
    applyArguments: % -> List %
    applyArgCount: % -> MachineInteger
    applyArgGet: (%, MachineInteger) -> %

    comma?: % -> Boolean
    newComma: List % -> %
    commaArguments: % -> List %
    commaArgCount: % -> MachineInteger
    commaArgGet: (%, MachineInteger) -> %

    declare?: % -> Boolean
    declareType: % -> %

    id?: % -> Boolean

    literal?: % -> Boolean
    newLiteral: String -> %
    literal: % -> String

    none?: % -> Boolean
    newNone: () -> %


AbSynCategory(T: PrimitiveType): Category == BaseAbSynCategory with
    idSymbol: % -> T
    newId: T -> %
    newDeclare: (T, %) -> %
    declareId: % -> T
    principalOperator: % -> T

    if T has SExpressionOutputType then SExpressionOutputType

AbSynAny(T: PrimitiveType): AbSynCategory(T) with
== add
    Application == Record(op: %, args: List %)
    Declare == Record(id: T, type: %)
    Comma == List %
    Lit == String
    Struct == Union(id: T, declare: Declare, app: Application, comma: Comma, lit: Lit, none: Cross())
    Rep == Record(fields: Fields %, struct: Struct)
    import from Rep, Application, Fields %, Declare

    apply?(ab: %): Boolean == rep(ab).struct case app
    applyOperator(ab: %): % == rep(ab).struct.app.op
    applyArguments(ab: %): List % == rep(ab).struct.app.args
    applyArgCount(ab: %): MachineInteger == # applyArguments ab
    applyArgGet(ab: %, n: MachineInteger): % == (applyArguments ab).(n+1)
    newApply(op: %, args: List %): % == per [newFields(), [[op, args]]]

    declare?(ab: %): Boolean == rep(ab).struct case declare
    newDeclare(id: T, type: %): % == per [newFields(), [[id, type]]]
    declareId(ab: %): T == rep(ab).struct.declare.id
    declareType(ab: %): % == rep(ab).struct.declare.type

    comma?(ab: %): Boolean == rep(ab).struct case comma
    newComma(l: List %): % == per [newFields(), [l]]
    commaArguments(ab: %): List % == rep(ab).struct.comma
    commaArgCount(ab: %): MachineInteger == # commaArguments ab
    commaArgGet(ab: %, n: MachineInteger): % == (commaArguments ab).(n+1)

    id?(ab: %): Boolean == rep(ab).struct case id -- rep(ab) case id
    newId(s: T): % == per [newFields(), [s]]
    idSymbol(ab: %): T == rep(ab).struct.id -- rep(ab).id

    newLiteral(s: String): % == per [newFields(), [s]]
    literal?(ab: %): Boolean == rep(ab).struct case lit
    literal(ab: %): String == rep(ab).struct.lit

    none?(ab: %): Boolean == rep(ab).struct case none
    newNone(): % == per [newFields(), [()@Cross()]]

    fields(ab: %): Fields % == rep(ab).fields

    (ab1: %) = (ab2: %): Boolean ==
        id? ab1 => id? ab2 and idSymbol ab1 = idSymbol ab2
        apply? ab1 => apply? ab2
                        and rep(ab1).struct.app.op = rep(ab2).struct.app.op
                        and rep(ab1).struct.app.args = rep(ab2).struct.app.args
        comma? ab1 => rep(ab1).struct.comma = rep(ab2).struct.comma
        literal? ab1 => literal? ab2 and literal ab1 = literal ab2
        declare? ab1 => declare? ab2 and declareId ab1 = declareId ab2 and declareType ab1 = declareType ab2
        none? ab1 => none? ab2
        error("Odd AbSyn for equality")

    if T has SExpressionOutputType then
        sexpression(ab: %): SExpression ==
            import from Symbol
            import from List %
            id? ab => sexpression idSymbol ab
            apply? ab => cons(sexpression applyOperator ab, [sexpression arg for arg in applyArguments ab])
            none? ab => nil
            literal? ab => sexpr literal ab
            declare? ab => [sexpr(-"Declare"), sexpression declareId ab, sexpression declareType ab]
            comma? ab => [sexpression part for part in commaArguments ab]
            error("odd absyn")

    principalOperator(ab: %): T ==
        apply? ab => principalOperator applyOperator ab
        id? ab => idSymbol ab
        never


AbSyn: AbSynCategory Symbol with
    SExpressionInputType
    SExpressionOutputType
== AbSynAny(Symbol) add

    sexpression(ab: %): SExpression ==
        import from List %, Symbol
        id? ab => sexpr idSymbol ab
        apply? ab => cons(sexpression applyOperator ab, [sexpression arg for arg in applyArguments ab])
        none? ab => nil
        literal? ab => sexpr literal ab
        declare? ab => [sexpr(-"Declare"), sexpr declareId ab, sexpression declareType ab]
        error("odd absyn")

    parseSExpression(sx: SExpression): % == parse(sx)$AbSynParser

AbSynParser: with
    parse: SExpression -> AbSyn
== add
    parse(sx: SExpression): AbSyn ==
        if cons? sx then parseCons(sx) else parseId(sx)

    local parseCons(sx: SExpression): AbSyn ==
        import from Symbol
        opSx := first sx
        opSx = sexpr(-":") => parseDeclare sx
        opSx = sexpr(-",") => parseComma sx
        parseApply sx

    local parseApply(sx: SExpression): AbSyn ==
        import from List AbSyn
        op: AbSyn := parse(first sx)
        args := [parse elt for elt in rest sx]
        newApply(op, args)

    local parseComma(sx: SExpression): AbSyn ==
        import from List AbSyn
        newComma [parse elt for elt in sx]

    local parseDeclare(sx: SExpression): AbSyn ==
        sx := rest sx
        (lhs, sx) := (first sx, rest sx)
        rhs := first sx
        newDeclare(sym lhs, parse rhs)

    local parseId(sx: SExpression): AbSyn ==
        import from Integer
        sym? sx => newId sym sx
        str? sx => newLiteral str sx
        int? sx => newLiteral toString int sx
        error("Parsing " + (toString sx))

AbSynOperations(Ab: BaseAbSynCategory): with
    map: ((Ab, Ab -> Ab) -> Ab) -> Ab -> Ab
== add
    import from List Ab
    map(f: (Ab, Ab -> Ab) -> Ab): Ab -> Ab ==
        local recurse(abi: Ab): Ab ==
            id? abi => f(abi, recurse)
            apply? abi =>
                op := f(applyOperator abi, recurse)
                args := [f(arg, recurse) for arg in applyArguments abi]
                newApply(op, args)
            abi
        (ab: Ab): Ab +-> f(ab, recurse)

#if 0
fixApply(ab: AnnotatedAbSyn, recurse: AnnotatedAbSyn -> AnnotatedAbSyn): AnnotatedAbSyn ==
    apply? ab and stuff() => applyOperator(ab)
    recurse(ab)
#endif
