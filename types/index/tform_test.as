#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib

import from AbSyn, SExpression, TForm, Symbol, MachineInteger, TypePackage, Export
import from BooleanFold, SymbolMeaning
import from Assert String, Partial TForm, List Export, List TForm, List SymbolMeaning
import from Assert MachineInteger, Assert(List, TForm), Assert(List, SymbolMeaning)

local annotate(env: Env)(ab: AbSyn): AnnotatedAbSyn ==
    import from AbSynAnnotator
    annotateSym(id: Symbol): AnnotatedId == newAnnotatedId(env, id)
    annotate(annotateSym, ab)

simpleTypeSystem(): TypeSystem == typeSystem()$SimpleTypeSystem

TestTypeLibrary: with
   create: (TypeSystem, Env) -> %
   List: % -> SymbolMeaning
   String: % -> SymbolMeaning
   BasicType: % -> SymbolMeaning
   find: % -> Symbol -> Partial TForm
== add
    Rep == HashTable(Symbol, SymbolMeaning)
    import from Rep, Symbol

    create(ts: TypeSystem, e: Env): % ==
        import from SymbolMeaning, BasicLibrary
        tbl := table()
        this := per tbl
        basicLibrary: ConstLibrary := constLibrary imports basicLibrary(ts, e)
        innerE := newEnv(find this, newEnv(lookup basicLibrary, e));
        lib: List SymbolMeaning := [BasicType(innerE), XList(innerE), String(innerE), ListType(innerE)]
        for syme in lib repeat tbl.(name syme) := syme
        this

    BasicType(env: Env): SymbolMeaning ==
        ts: TypeSystem := simpleTypeSystem()
        self: TForm := newSyntax(ts, (annotate env) parseSExpression fromString "%")
        sample: TForm := newSignature(-"sample",
                             newMap([], [self]), [])
        myForm: TForm  := newSyntax(ts, (annotate env) parseSExpression fromString "BasicType")
        thd := newThird([myForm, sample])
        newSymbolMeaning(-"BasicType", thd)

    XList(env: Env): SymbolMeaning ==
        import from TForm, SExpression, AbSyn, Symbol, List TForm
        ts: TypeSystem := simpleTypeSystem()
        self: TForm := newSyntax(ts, (annotate env) parseSExpression fromString "%")
        arg: TForm := newSyntax(ts, (annotate env) parseSExpression fromString "#1")
        cons: TForm := newSignature(-"cons",
                             newMap([arg, self], [self]), [])
        first := newSignature(-"first", newMap([self], [arg]), [])
        rest := newSignature(-"rest",  newMap([self], [self]), [])
        ListType := newSyntax(ts, (annotate env) parseSExpression fromString "(ListType #1)")
        cat := newCategory([ListType, cons, first, rest])
        cat0 := bind(cat, (annotate env) parseSExpression fromString "(List #1)")
        BasicTypeSyntax: TForm := newSyntax(ts, (annotate env) parseSExpression fromString "BasicType")
        newSymbolMeaning(-"List", newMap([newDeclare(-"#1", BasicTypeSyntax)], [cat0]))

    ListType(env: Env): SymbolMeaning ==
        import from TForm, SExpression, AbSyn, Symbol, List TForm
        ts: TypeSystem := simpleTypeSystem()
        self: TForm := newSyntax(ts, (annotate env) parseSExpression fromString "%")
        arg: TForm := newSyntax(ts, (annotate env) parseSExpression fromString "#1")
        first := newSignature(-"first", newMap([self], [arg]), [])
        rest := newSignature(-"rest",  newMap([self], [self]), [])
        BasicTypeSyntax: TForm := newSyntax(ts, (annotate env) parseSExpression fromString "BasicType")
        myForm: TForm          := newSyntax(ts, (annotate env) parseSExpression fromString "(ListType #1)")
        thd := newThird([myForm, BasicTypeSyntax])
        newSymbolMeaning(-"ListType", newMap([newDeclare(-"#1", BasicTypeSyntax)], [thd]))

    --- Foo(X: A): Category == with... ==> : Third(with ...)

    String(env: Env): SymbolMeaning ==
        import from TForm, SExpression, AbSyn, Symbol, List TForm
        ts: TypeSystem := simpleTypeSystem()
        self: TForm := newSyntax(ts, (annotate env) parseSExpression fromString "%")
        BasicTypeSyntax: TForm := newSyntax(ts, (annotate env) parseSExpression fromString "BasicType")
        newSymbolMeaning(-"String", bind(newCategory [BasicTypeSyntax], (annotate env) parseSExpression fromString "String"))

    find(lib: %)(sym: Symbol): Partial TForm ==
        import from SymbolMeaning
        stdout << "BasicLib::Lookup: " << sym << " " << find(sym, rep lib) << newline
        r: Partial SymbolMeaning := find(sym, rep lib)
        failed? r => failed
        [type retract r]

    String(l: %): SymbolMeaning == rep(l).(-"String")
    List(l: %): SymbolMeaning == rep(l).(-"List")
    BasicType(l: %): SymbolMeaning == rep(l).(-"BasicType")

basicEnv(): Env ==
    import from TypePackage
    sat: FnSatisfier := (satisfier$SimpleSatisfier)::FnSatisfier
    envInferFn(ab: AnnotatedAbSyn): TForm == infer(sat, ab)
    basicLib: TestTypeLibrary := create(simpleTypeSystem(), emptyEnv(envInferFn))
    basicEnv := newEnv(find(basicLib), emptyEnv(envInferFn))
    basicEnv

test(): () ==
    env := basicEnv()
    ts: TypeSystem := simpleTypeSystem()
    ab: AnnotatedAbSyn := (annotate env) parseSExpression(fromString "(List #1)")
    tf := newSyntax(ts, ab)
    sigma: AbSub := newSubst(-"#1", (annotate env) parseSExpression fromString "S")
    stdout << tf << newline
    stdout << subst(tf, sigma) << newline
    assertEquals(toString subst(tf, sigma), "{(List S)}")


test2(): () ==
    env: Env := basicEnv()
    ab: AnnotatedAbSyn := (annotate env) parseSExpression fromString "String"
    tt := infer(env, ab)
    stdout << "Infered: " << tt << newline
    stdout << "Parents: " << pp << newline where pp := allCatParents tt

test3(): () ==
    env: Env := basicEnv()
    ab: AnnotatedAbSyn := (annotate env) parseSExpression fromString "(List String)"
    tt := infer(env, ab)
    stdout << "Infered: " << tt << newline
    stdout << "Parents: " << allCatParents tt << newline

testStringTypeParents(): () ==
    env: Env := basicEnv()
    tf: TForm := retract lookup(env, -"String")
    stdout << "string tf " << tf << " " << newline
    stdout << "string parents " << directCatParents tf << " " << newline
    assertEquals(1, # directCatParents tf)
    assertEquals("{BasicType}", toString type first directCatParents tf)

testListStringTypeParents(): () ==
    import from TfSignature
    env: Env := basicEnv()
    tf: TForm := infer(env, (annotate env) parseSExpression fromString "(List String)")
    tfListType: TForm := newSyntax(simpleTypeSystem(), (annotate env) parseSExpression fromString "(ListType String)")
    stdout << "string tf " << tf << " " << newline
    stdout << "string parents " << directCatParents tf << " " << newline
    assertEquals(4, # directCatParents tf)
    assertTrue(_or/( (tfListType = type exp) for exp in directCatParents tf))
    assertTrue(_or/( (name signature((type exp)::TfSignature) = -"cons") for exp in directCatParents tf | signature? type exp))
    assertTrue(_or/( (name signature((type exp)::TfSignature) = -"first") for exp in directCatParents tf | signature? type exp))
    assertTrue(_or/( (name signature((type exp)::TfSignature) = -"rest") for exp in directCatParents tf | signature? type exp))

testListTypeParents(): () ==
    import from TfSignature
    env: Env := basicEnv()
    tf: TForm := newSyntax(simpleTypeSystem(), (annotate env) parseSExpression fromString "(ListType String)")
    tfBasicType: TForm := newSyntax(simpleTypeSystem(), (annotate env) parseSExpression fromString "BasicType")
    stdout << "string tf " << tf << " " << newline
    stdout << "string parents " << pp << " " << newline where pp := directCatParents tf
    assertEquals(2, # directCatParents tf)
    assertTrue(_or/( (tf = type exp) for exp in directCatParents tf))
    assertTrue(_or/( (tfBasicType = type exp) for exp in directCatParents tf))

testStringImports(): () ==
    env: Env := basicEnv()
    tf: TForm := retract lookup(env, -"String")
    tfString: TForm := newSyntax(simpleTypeSystem(), (annotate env) parseSExpression fromString "String")
    stdout << "string tf " << tf << " " << newline
    stdout << "string imports " << ii << " " << newline where ii := imports tf
    assertSizeEquals(1, imports tf)
    assertMember(newSymbolMeaning(-"sample", newMap([], [tfString])), imports tf)

testListStringImports(): () ==
    env: Env := basicEnv()
    ab: AnnotatedAbSyn := (annotate env) parseSExpression fromString "(List String)"
    tf := infer(env, ab)
    stdout << "string tf " << tf << " " << newline
    stdout << "string imports " << ii << " " << newline where ii := imports tf
    assertSizeEquals(4, imports tf)

test()
test2()
test3()
testStringTypeParents()
testListStringTypeParents()
testListTypeParents()
testStringImports()
testListStringImports()
