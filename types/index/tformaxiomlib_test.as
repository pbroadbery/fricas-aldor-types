#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib

basicTypeSystem(): TypeSystem == typeSystem()$SimpleTypeSystem

emptyEnv(): Env ==
    import from TypePackage
    sat: FnSatisfier := (satisfier$SimpleSatisfier)::FnSatisfier
    envInferFn(ab: AnnotatedAbSyn): TForm == infer(sat, ab)
    emptyEnv(envInferFn)

simpleEnv(): Env ==
    import from TypePackage, ConstLibrary
    sat: FnSatisfier := (satisfier$SimpleSatisfier)::FnSatisfier
    envInferFn(ab: AnnotatedAbSyn): TForm == infer(sat, ab)
    empty := emptyEnv(envInferFn)
    basicEnv: BasicLibrary := basicLibrary(basicTypeSystem(), empty)
    newEnv(lookup constLibrary imports basicEnv, empty)

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
    import from AbSyn, SExpression, TForm, Symbol
    import from String, TypePackage
    import from List Export
    import from Assert String

    env: Env := simpleEnv()

    lib: AxiomLibrary := newLibrary(basicTypeSystem(), env, "/home/pab/Work/fricas/build/src/algebra")
    e2: Env := env lib
    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "String"
    integer := infer(e2, ab)

    stdout << "inferred integer: " << integer << newline
    stdout << "imports of List Integer: " << catExports integer << newline

    --error "Need some tests here"

test2(): () ==
    import from TypePackage, AbSyn, SExpression, TForm, Symbol
    import from Assert String
    import from List Export
    env := simpleEnv()
    ts: TypeSystem := basicTypeSystem()
    lib: AxiomLibrary := newLibrary(ts, env, "/home/pab/Work/fricas/build/src/algebra")
    e2 := env lib
    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "(List Integer)"
    listInteger: TForm := newSyntax(ts, ab)

    stdout << "imports of List Integer: " << catExports listInteger << newline

    --error "Need some tests here"

test3(): () ==
    import from AbSyn, SExpression, TForm, Symbol, Assert String
    import from String, List Export, Symbol
    env: Env := simpleEnv()
    ts: TypeSystem := basicTypeSystem()
    lib: AxiomLibrary := newLibrary(ts, env, "/home/pab/Work/fricas/build/src/algebra")
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), env)

    aa: Partial TForm := lookup(e2, -"String")
    stdout << "string " << aa << newline
    type: TForm:= Type$TForm
    theString: TForm := newSyntax(ts, (annotate e2) parseSExpression sexpr(-"String"))

    assertSatisfies(theString, type)
    assertDoesNotSatisfy(type, theString)

    mapStrToStr: TForm := newSyntax(ts, (annotate e2) parseSExpression fromString "(Map String String)")

    assertSatisfies(mapStrToStr, type)
    assertDoesNotSatisfy(type, mapStrToStr)
    assertDoesNotSatisfy(theString, mapStrToStr)

testShowLibrary(): () ==
    import from List Symbol
    import from Partial TForm
    import from Symbol, TfMap, TypeInfo, TfThird
    env: Env := simpleEnv()
    ts: TypeSystem := basicTypeSystem()
    lib: AxiomLibrary := newLibrary(ts, env, "/home/pab/Work/fricas/build/src/algebra")
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), env)

    for id in ids lib repeat
        tf: TForm := retract tform(lib, id)
        stdout << "DomImports: " << tf << newline
        if map? tf then
            stdout << "Map: " << tf << newline
        else if category?(typeInfo tf, tf) then
            imps: List SymbolMeaning := imports(tf)$TypePackage
            stdout << imps << newline
        else if third?(tf)$TfThird then
            thds: List Export := thdExports(tf::TfThird)
            stdout << thds << newline
        else
            stdout << domImports tf << newline

testTypeMap(): () ==
    import from AbSyn, SExpression, TForm, Symbol, Assert String
    import from String, List TForm

    env: Env := simpleEnv()

    lib: AxiomLibrary := newLibrary(basicTypeSystem(), env, "/home/pab/Work/fricas/build/src/algebra")
    e2: Env := env lib
    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "ListAggregate"
    aggType := infer(e2, ab)
    stdout << "inferred string: " << aggType << newline

    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "SetCategory"
    aggType := infer(e2, ab)
    stdout << "inferred string: " << aggType << newline

testParents1(): () ==
    import from AbSyn, SExpression, TForm, Symbol, Assert String
    import from String, List TForm
    import from TypePackage
    env: Env := simpleEnv()

    lib: AxiomLibrary := newLibrary(basicTypeSystem(), env, "/home/pab/Work/fricas/build/src/algebra")
    e2: Env := env lib
    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "String"
    stringType := infer(e2, ab)

    stdout << "inferred string: " << stringType << newline

    stdout << "parents of String: " << allParents stringType << newline

assertSatisfies(S: TForm, T: TForm): () ==
    import from GeneralAssert
    satisfies ==> (satisfier$SimpleSatisfier)
    r: SatResult := satisfies(S, T)
    stdout << "Satisfies: " << S << " sat " << T << " = " << r << newline
    assertTrue(success? r)

assertDoesNotSatisfy(S: TForm, T: TForm): () ==
    import from GeneralAssert
    satisfies ==> (satisfier$SimpleSatisfier)
    r: SatResult := satisfies(S, T)
    stdout << "Satisfies: " << S << " sat " << T << " = " << r << newline
    assertFalse(success? r)

test1()
test2()
test3()
testTypeMap()
testParents1()
--testShowLibrary()
