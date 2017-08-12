#include "aldor"
#include "aldorio"
#library BITS "bitset.ao"
#pile

import from BITS

Match(T: Type): with
    match: T -> %
    value: % -> T
== add
    Rep == T
    match(x: T): % == per x
    value(m: %): T == rep m

Pattern(T: Type): with
    case: (Match T, %) -> Boolean
    value: % -> T
    pattern: (T -> Boolean) -> %
    evaluate: (%, T) -> Boolean
== add
    Rep == Union(val: Partial T, evaluate: T -> Boolean)
    import from Rep, Partial T

    pattern(f: T -> Boolean): % == per [f]
    case(m: Match T, p: %): Boolean == evaluate(p, value m)

    evaluate(p: %, t: T): Boolean ==
        res := rep(p).evaluate(t)
        rep(p).val := if res then [t] else failed
        res

    value(p: %): T == retract rep(p).val

Patterns: with
    any: (T: Type) -> Pattern T
== add
    any(T: Type): Pattern T == pattern( (x: T): Boolean +-> true);

