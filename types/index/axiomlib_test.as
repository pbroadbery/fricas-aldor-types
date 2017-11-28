#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib

import from HashTable(Symbol, SExpression)
import from Symbol, SExpression, LibAttribute, TfSignature
import from AbSyn, TypePackage
import from List HashTable(Symbol, SExpression), List TForm, List SymbolMeaning, List Export
import from Assert Symbol, Assert TForm

basicEnv(): Env ==
    import from TypePackage, ConstLibrary
    sat: FnSatisfier := (satisfier$SimpleSatisfier)::FnSatisfier
    envInferFn(ab: AnnotatedAbSyn): TForm == infer(sat, ab)
    empty := emptyEnv(envInferFn)
    basicEnv: BasicLibrary := basicLibrary(simpleTypeSystem(), empty)
    newEnv(lookup constLibrary imports basicEnv, empty)

local simpleTypeSystem(): TypeSystem == typeSystem()$SimpleTypeSystem

local annotate(env: Env)(ab: AbSyn): AnnotatedAbSyn ==
    import from AbSynAnnotator
    annotateSym(id: Symbol): AnnotatedId == newAnnotatedId(env, id)
    annotate(annotateSym, ab)

-- simple1: value: %
local simple1: HashTable(Symbol, SExpression) ==
    [(symbol libAttrAbbreviation, fromString "SIMPL1"),
     (symbol libAttrConstructorForm, fromString "(|Simple1|)"),
     (symbol libAttrConstructorKind, fromString "domain"),
     (symbol libAttrConstructorModemap, fromString("(((|Simple1|) (CATEGORY |domain| (SIGNATURE |value| ($) |constant|)))"
                                               + "(T |Simple1|))")),
     (symbol libAttrOperationAlist, fromString "((|value| (($) 7 T CONST)))"),
     (symbol libAttrParents, fromString "()")
     ]

-- simple2: fn: % -> %
local simple2: HashTable(Symbol, SExpression) ==
    [(symbol libAttrAbbreviation, fromString "SIMPL2"),
     (symbol libAttrConstructorForm, fromString "(|Simple2|)"),
     (symbol libAttrConstructorKind, fromString "domain"),
     (symbol libAttrConstructorModemap, fromString("(((|Simple2|) (CATEGORY |domain| (SIGNATURE |plus| ($ $ $)))) (T |Simple2|))")),
     (symbol libAttrOperationAlist, fromString "((|plus| (($ $ $) 7)))"),
     (symbol libAttrParents, fromString "()")
     ]

-- csimple2: fn: % -> %
local csimple3: HashTable(Symbol, SExpression) ==
    [(symbol libAttrAbbreviation, fromString "CSIMPL3"),
     (symbol libAttrConstructorForm, fromString "(|CSimple3|)"),
     (symbol libAttrConstructorKind, fromString "category"),
     (symbol libAttrConstructorModemap, fromString("(((|CSimple3|) (|Category|)) (T |CSimple3|))")),
     (symbol libAttrOperationAlist, fromString "((|f| (($ $) 6)))"),
     (symbol libAttrParents, fromString "()")
     ]

-- csimple9: fn: Int -> Union(%, "failed")
local csimple9: HashTable(Symbol, SExpression) ==
    [(symbol libAttrAbbreviation, fromString "CSIMPL9"),
     (symbol libAttrConstructorForm, fromString "(|CSimple9|)"),
     (symbol libAttrConstructorKind, fromString "category"),
     (symbol libAttrConstructorModemap, fromString("(((|CSimple9|) (|Category|)) (T |CSimple9|))")),
     (symbol libAttrOperationAlist, fromString "((|partial| (((|Union| $ _"failed_") (|Integer|)) 6)))"),
     (symbol libAttrParents, fromString "()")
     ]

-- simple10: fn: Int -> Union(%, "failed")
local simple10: HashTable(Symbol, SExpression) ==
    [(symbol libAttrAbbreviation, fromString "SIMPL10"),
     (symbol libAttrConstructorForm, fromString "(|Simple10|)"),
     (symbol libAttrConstructorKind, fromString "package"),
     (symbol libAttrConstructorModemap, fromString("(((|Simple10|) (CATEGORY |package| (SIGNATURE |variable| ((|Union| (|Integer|) _"failed_") (|Integer|))))) (T |Simple10|))")),
     (symbol libAttrOperationAlist, fromString "((|partial| (((|Union| $ _"failed_") (|Integer|)) 6)))"),
     (symbol libAttrParents, fromString "()")
     ]

-- csimple11: CSimple11(X: CSimple8): Category == CSimple4 with f: () -> ()
local csimple11: HashTable(Symbol, SExpression) ==
    [(symbol libAttrAbbreviation, fromString "CSMP11"),
     (symbol libAttrConstructorForm, fromString "(|CSimple11|)"),
     (symbol libAttrConstructorKind, fromString "category"),
     (symbol libAttrConstructorModemap, fromString("(((|CSimple11| |#1|) (|Category|) (|CSimple3|)) (T |CSimple11|))")),
     (symbol libAttrOperationAlist, fromString "((|f| (($ $) 6) (((|@Tuple|)) 6)))"),
     (symbol libAttrParents, fromString "(((|CSimple9|) . T))")
     ]



local tfGeneral(e0: Env, s: String): TForm ==
    import from AbSyn
    ab: AnnotatedAbSyn := (annotate e0) parseSExpression fromString s
    newSyntax(simpleTypeSystem(), ab)

test0(): () ==
    import from List HashTable(Symbol, SExpression), List SymbolMeaning
    import from Assert TForm
    import from Partial TForm
    import from Symbol, SExpression, AbSyn, SymbolMeaning, TypePackage

    e0: Env := basicEnv()
    ts: TypeSystem := simpleTypeSystem()
    lib: AxiomLibrary := newLibrary(ts, e0, [simple1])
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), e0)

    tf: TForm := retract tform(lib, -"Simple1")
    tf2 := tfGeneral(e2, "(Simple1)")
    ii := imports tf
    stdout << "imports " << ii << newline
    assertEquals(type first ii, tf2)

test1(): () ==
    import from List HashTable(Symbol, SExpression), List SymbolMeaning, List TForm
    import from Assert TForm
    import from Partial TForm
    import from Symbol, SExpression, AbSyn, SymbolMeaning, TypePackage

    e0: Env := basicEnv()
    ts: TypeSystem := simpleTypeSystem()

    lib: AxiomLibrary := newLibrary(ts, e0, [simple2])
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), e0)

    tf: TForm := retract tform(lib, -"Simple2")
    self := tfGeneral(e2, "(Simple2)")
    tf2 := newMap(newMulti([self, self]), self)
    assertEquals(type first imports tf, tf2)

test2(): () ==
    e0: Env := basicEnv()
    ts: TypeSystem := simpleTypeSystem()

    lib: AxiomLibrary := newLibrary(ts, e0, [simple2])
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), e0)

    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "Simple2"
    tf2: TForm := infer(e2, ab)
    self: TForm := tfGeneral(e2, "(Simple2)")
    stdout << "imports " << ii << newline where ii := imports tf2
    plus: SymbolMeaning := first imports tf2
    assertEquals(-"plus", name plus)
    assertEquals(newMap(newMulti [self, self], self), type plus)

test3(): () ==
    e0: Env := basicEnv()
    ts: TypeSystem := simpleTypeSystem()

    lib: AxiomLibrary := newLibrary(ts, e0, [csimple3])
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), e0)

    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "CSimple3"
    tf: TForm := newSyntax(ts, ab)

    stdout << "Type is: " << tf << newline
    stdout << "parents: " << imps << newline where imps := directCatParents tf
    self: TForm := tfGeneral(e2, "%")
    f: Export := signature(type first([exp for exp in directCatParents tf | signature? type exp])::TfSignature)
    assertEquals(-"f", name f)
    assertEquals(newMap([self], [self]), type f)


test9(): () ==
    import from AbSyn, Symbol, TypePackage
    import from Partial TForm
    import from List HashTable(Symbol, SExpression)
    import from List Export, List TForm, List SymbolMeaning
    import from Assert Symbol, Assert TForm
    e0: Env := basicEnv()
    ts: TypeSystem := simpleTypeSystem()

    lib: AxiomLibrary := newLibrary(ts, e0, [csimple9])
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), e0)

    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "CSimple9"
    tf: TForm := newSyntax(ts, ab)

    stdout << "Type is: " << tf << newline
    stdout << "catExports: " << imps << newline where imps := imports tf
    self: TForm := tfGeneral(e2, "%")
    integer: TForm := tfGeneral(e2, "Integer")
    f: SymbolMeaning := first imports tf
    assertEquals(-"partial", name f)
    --assertEquals(newMap(self, self), type f)

test10(): () ==
    import from AbSyn, Symbol, TypePackage
    import from Partial TForm
    import from Assert Symbol, Assert TForm
    import from List HashTable(Symbol, SExpression)
    import from List Export, List TForm, List SymbolMeaning

    e0: Env := basicEnv()
    ts: TypeSystem := simpleTypeSystem()

    lib: AxiomLibrary := newLibrary(ts, e0, [simple10])
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), e0)

    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "Simple10"
    tf: TForm := newSyntax(ts, ab)
    cat: TForm := infer(e2, ab)

    stdout << "Type is: " << tf << newline
    stdout << "domExports: " << domExps << newline where domExps := imports(cat)$TypePackage
    stdout << "Cat is: " << cat << newline
    stdout << "catExports: " << catExps << newline where catExps := allCatParents cat
    self: TForm := tfGeneral(e2, "%")
    integer: TForm := tfGeneral(e2, "Integer")
    f: Export := first allCatParents tf
    assertEquals(-"partial", name f)
    --assertEquals(newMap(self, self), type f)


test11(): () ==
    import from AbSyn, Symbol, TypePackage
    import from Partial TForm
    import from List HashTable(Symbol, SExpression)
    import from List Export, List TForm, List SymbolMeaning
    import from Assert Symbol, Assert TForm
    e0: Env := basicEnv()
    ts: TypeSystem := simpleTypeSystem()

    lib: AxiomLibrary := newLibrary(ts, e0, [csimple11, csimple3, csimple9])
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), e0)

    tf: TForm := retract lookup(e2, -"CSimple11")
    stdout << "TF 11 " << tf << newline


test0()
test1()
test2()
test3()
--test9()
--test10()

test11()
