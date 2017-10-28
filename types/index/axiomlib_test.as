#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib

import from HashTable(Symbol, SExpression)
import from Symbol, SExpression, LibAttribute

basicEnv(): Env ==
    import from TypePackage
    sat: FnSatisfier := (satisfier$SimpleSatisfier)::FnSatisfier
    envInferFn(ab: AnnotatedAbSyn): TForm == infer(sat, ab)
    emptyEnv(envInferFn)

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
     --(symbol modemaps, fromString "((|value| (*1 *1) (|isDomain| *1 (|Simple1|))))"),
     ]

-- simple2: fn: % -> %
local simple2: HashTable(Symbol, SExpression) ==
    [(symbol libAttrAbbreviation, fromString "SIMPL2"),
     (symbol libAttrConstructorForm, fromString "(|Simple2|)"),
     (symbol libAttrConstructorKind, fromString "domain"),
     (symbol libAttrConstructorModemap, fromString("(((|Simple2|) (CATEGORY |domain| (SIGNATURE |plus| ($ $ $)))) (T |Simple2|))")),
     (symbol libAttrOperationAlist, fromString "((|plus| (($ $ $) 7)))"),
     (symbol libAttrParents, fromString "()")
     --(symbol modemaps, fromString "((|value| (*1 *1) (|isDomain| *1 (|Simple1|))))"),
     ]


local tfGeneral(e0: Env, s: String): TForm ==
    import from AbSyn
    ab: AnnotatedAbSyn := (annotate e0) parseSExpression fromString s
    newSyntax ab

test0(): () ==
    import from List HashTable(Symbol, SExpression)
    import from List Export
    import from Assert TForm
    import from Partial TForm
    import from Symbol, SExpression, AbSyn, Export

    e0: Env := basicEnv()
    lib: AxiomLibrary := newLibrary(e0, [simple1])
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), e0)

    tf: TForm := retract tform(lib, -"Simple1")
    tf2 := tfGeneral(e2, "$")
    stdout << "Simple1: " << tf << newline
    stdout << "Simple1: " << catExports tf << newline

    stdout << "types " << tf2 << " lib " << type first catExports tf << newline
    stdout << "types eq " << (tf2 = type first catExports tf) << newline
    assertEquals(type first catExports tf, tf2)

test1(): () ==
    import from List HashTable(Symbol, SExpression)
    import from List Export
    import from List TForm
    import from Assert TForm
    import from Partial TForm
    import from Symbol, SExpression, AbSyn, Export

    e0: Env := basicEnv()
    lib: AxiomLibrary := newLibrary(e0, [simple2])
    e2: Env := newEnv((sym: Symbol): Partial TForm +-> tform(lib, sym), e0)

    tf: TForm := retract tform(lib, -"Simple2")
    self := tfGeneral(e2, "$")
    tf2 := newMap(newMulti([self, self]), self)
    stdout << "Simple1: " << tf << newline
    stdout << "Simple1: " << catExports tf << newline

    stdout << "types " << tf2 << " lib " << type first catExports tf << newline
    stdout << "types eq " << (tf2 = type first catExports tf) << newline
    assertEquals(type first catExports tf, tf2)

test0()
test1()

