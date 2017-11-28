#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib

import from AbSyn, SExpression, TForm, Symbol, Export
import from String, TypePackage
import from List Export, List SymbolMeaning
import from Assert String
import from BooleanFold

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
    env: Env := simpleEnv()

    lib: AxiomLibrary := newLibrary(basicTypeSystem(), env, "/home/pab/Work/fricas/build/src/algebra")
    e2: Env := env lib
    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "String"
    str := infer(e2, ab)

    stdout << "inferred integer: " << str << newline
    stdout << "imports of List Integer: " << imports str << newline

    --error "Need some tests here"

test2(): () ==
    env: Env := simpleEnv()
    ts: TypeSystem := basicTypeSystem()
    lib: AxiomLibrary := newLibrary(ts, env, "/home/pab/Work/fricas/build/src/algebra")
    e2: Env := env lib
    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "(List Integer)"
    listInteger: TForm := infer(e2, ab)

    stdout << "imports of List Integer: " << imports listInteger << newline

    --error "Need some tests here"

test3(): () ==
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
            thds: List Export := thdParents(tf::TfThird)
            stdout << thds << newline
        else
            stdout << imports tf << newline

testTypeMap(): () ==
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
    stdout << "parents of String: " << directCatParents stringType << newline

testParents2(): () ==
    import from AbSyn, SExpression, TForm, Symbol, Assert String
    import from String, TfThird, List TForm
    import from TypePackage
    import from Partial TForm
    env: Env := simpleEnv()

    lib: AxiomLibrary := newLibrary(basicTypeSystem(), env, "/home/pab/Work/fricas/build/src/algebra")
    e2: Env := env lib
    stringCategory: TForm := retract lookup(e2, -"StringCategory")

    openMath: TForm := newSyntax(basicTypeSystem(), (annotate e2) parseSExpression fromString "OpenMath")
    stringAggregate: TForm := newSyntax(basicTypeSystem(), (annotate e2) parseSExpression fromString "StringAggregate")

    pp := thdParents(stringCategory::TfThird)
    stdout << "inferred string: " << stringCategory << newline
    stdout << "parents of String: " << pp << newline
    assertTrue( _or/ (openMath = type p for p in pp))
    assertTrue( _or/ (stringAggregate = type p for p in pp))

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
testParents2()
testShowLibrary()

