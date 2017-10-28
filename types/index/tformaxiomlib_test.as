#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib

emptyEnv(): Env ==
    import from TypePackage
    sat: FnSatisfier := (satisfier$SimpleSatisfier)::FnSatisfier
    envInferFn(ab: AnnotatedAbSyn): TForm == infer(sat, ab)
    emptyEnv(envInferFn)

simpleEnv(): Env ==
    import from Symbol
    type: TForm := Type$TForm
    category: TForm := Category$TForm
    tbl: HashTable(Symbol, TForm) := [(-"Type", type), (-"Category", category)]
    envFn(sym: Symbol): Partial TForm == find(sym, tbl)
    newEnv(envFn, emptyEnv())

local annotate(env: Env)(ab: AbSyn): AnnotatedAbSyn ==
    import from AbSynAnnotator
    annotateSym(id: Symbol): AnnotatedId == newAnnotatedId(env, id)
    annotate(annotateSym, ab)

test0(): () ==
    import from Directory
    dd := listDirectory "/home/pab/Work/fricas/build/src/algebra"
    import from List FileName, FileName
    for f in dd repeat stdout << f << newline

test0()


test1(): () ==
    import from AbSyn, SExpression, TForm, Symbol, Assert String
    import from String, List Export

    env: Env := simpleEnv()
    lib: AxiomLibrary := newLibrary(env, "/home/pab/Work/fricas/build/src/algebra")
    e2 := env lib
    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "String"
    integer := infer(e2, ab)

    stdout << "inferred integer: " << integer << newline
    stdout << "imports of List Integer: " << catExports integer << newline

    error "Need some tests here"

test2(): () ==
    import from AbSyn, SExpression, TForm, Symbol, Assert String
    import from String, List Export
    env := simpleEnv()
    lib: AxiomLibrary := newLibrary(env, "/home/pab/Work/fricas/build/src/algebra")
    e2 := env lib
    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "(List Integer)"
    listInteger: TForm := newSyntax(ab)

    stdout << "imports of List Integer: " << catExports listInteger << newline

    error "Need some tests here"

test3(): () ==
    import from AbSyn, SExpression, TForm, Symbol, Assert String
    import from String, List Export, Symbol
    env: Env := simpleEnv()
    lib: AxiomLibrary := newLibrary(env, "/home/pab/Work/fricas/build/src/algebra")
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), env)

    aa: Partial TForm := lookup(e2, -"String")
    stdout << "string " << aa << newline
    type: TForm:= newSyntax((annotate e2) parseSExpression sexpr(-"Type"))
    theString: TForm := newSyntax((annotate e2) parseSExpression sexpr(-"String"))
    satisfies ==> (satisfier$SimpleSatisfier)

    assertFalse(satisfies(theString, type))
    assertFalse(satisfies(type, theString))

    mapStrToStr: TForm := newSyntax((annotate e2) parseSExpression fromString "(Map String String)")

    assertTrue(satisfies(mapStrToStr, type))
    assertFalse(satisfies(type, mapStrToStr))
    assertFalse(satisfies(theString, mapStrToStr))

-- for now
assertTrue(r: SatResult): () ==
    stdout << r << newline

assertFalse(r: SatResult): () ==
    stdout << r << newline

test1()
--test2()
--test3()
