#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib

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
        lib: List SymbolMeaning := [BasicType(innerE), XList(innerE), String(innerE)]
        for syme in lib repeat tbl.(name syme) := syme
        this

    BasicType(env: Env): SymbolMeaning ==
        import from TForm, SExpression, AbSyn, Symbol, List TForm
        -- not strictly correct. (:Category == with {} & BasicType)
        newSymbolMeaning(-"BasicType", bind(Category$TForm, (annotate env) parseSExpression fromString "BasicType"))

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
        myForm := (annotate env) parseSExpression fromString "(ListType #1)"
        thd := newThird([newCategory [cat0]])
        newSymbolMeaning(-"ListType", newMap([newDeclare(-"#1", BasicTypeSyntax)], [cat0]))


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
    import from AbSyn, SExpression, TForm, Symbol, Assert String
    env := basicEnv()
    ts: TypeSystem := simpleTypeSystem()
    ab: AnnotatedAbSyn := (annotate env) parseSExpression(fromString "(List #1)")
    tf := newSyntax(ts, ab)
    sigma: AbSub := newSubst(-"#1", (annotate env) parseSExpression fromString "S")
    stdout << tf << newline
    stdout << subst(tf, sigma) << newline
    assertEquals(toString subst(tf, sigma), "{(List S)}")

test2(): () ==
    import from AbSyn, SExpression, TForm, Symbol, Assert String, List TForm
    env: Env := basicEnv()
    ab: AnnotatedAbSyn := (annotate env) parseSExpression fromString "String"
    tt := infer(env, ab)
    stdout << "Infered: " << tt << newline
    exps: List Export := catExports(tt)
    stdout << "Exports: " << exps << newline
    stdout << "Parents: " << catParents tt << newline

test3(): () ==
    import from AbSyn, SExpression, TForm, Symbol, Assert String, List TForm
    env: Env := basicEnv()
    ab: AnnotatedAbSyn := (annotate env) parseSExpression fromString "(List String)"
    tt := infer(env, ab)
    stdout << "Infered: " << tt << newline
    exps: List Export := catExports(tt)
    stdout << "Exports: " << exps << newline
    stdout << "Parents: " << catParents tt << newline

test()
test2()
test3()
