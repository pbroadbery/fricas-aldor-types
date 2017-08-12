#include "aldor"
#include "aldorio"
#library BITS "bitset.ao"
#library P3 "pattern3.ao"
#pile

import from BITS, P3
inline from BITS, P3

Ab: with
    parse: String -> %
    lit: Pattern String -> Pattern %
    pair: (Pattern String, Pattern %) -> Pattern %
== add
    Rep == Union(l: String, pair: Cross(String, %))
    import from Rep

    parse(txt: String): % == per [txt]

    lit(s: Pattern String): Pattern % ==
        import from Pattern String
        pattern( (ab: %): Boolean +-> rep(ab) case l and evaluate(s, rep(ab).l))

    pair(lhs: Pattern String, rhs: Pattern %): Pattern % ==
        pattern( (ab: %): Boolean +-> {
            not (rep(ab) case pair) => false;
            (l, r) := rep(ab).pair;
            evaluate(lhs, l) and evaluate(rhs, r)})


trial(): () ==
    import from Match Ab, Pattern Ab, Patterns, Pattern String
    x: Ab := parse("hello")
    select match(x) in
        lit(foo := any(String)) => value(foo)
        pair(lhs := any(String), rhs := any(Ab)) => value(lhs)
        never
