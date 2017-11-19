#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib

import from HashTable(Symbol, SExpression)
import from Symbol, SExpression, LibAttribute

local basicEnv(): Env ==
    import from TypePackage
    sat: FnSatisfier := (satisfier$SimpleSatisfier)::FnSatisfier
    envInferFn(ab: AnnotatedAbSyn): TForm == infer(sat, ab)
    emptyEnv(envInferFn)

local simpleTypeSystem(): TypeSystem == typeSystem()$SimpleTypeSystem

local annotate(env: Env)(ab: AbSyn): AnnotatedAbSyn ==
    import from AbSynAnnotator
    annotateSym(id: Symbol): AnnotatedId == newAnnotatedId(env, id)
    annotate(annotateSym, ab)

test0(): () ==
    import from BasicLibrary, AbSyn
    e0: Env := basicEnv()
    ts: TypeSystem := simpleTypeSystem()
    bs: ConstLibrary := constLibrary imports basicLibrary(ts, e0)
    e2: Env := newEnv(lookup bs, e0)

    ab: AnnotatedAbSyn := (annotate e2) parseSExpression fromString "(Record Type Type)"

    stdout << type << newline where type: TForm := infer(e2, ab)



test0()