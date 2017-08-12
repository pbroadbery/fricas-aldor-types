#include "aldor"
#include "aldorio"
#pile

Pattern(T: with, O: PatternOutputCategory): with
== add

PatternOutputCategory: Category == with

None: PatternOutputCategory with == add
Value(T: with): PatternOutputCategory with == add
Pair(O1: PatternOutputCategory, O2: PatternOutputCategory): PatternOutputCategory with == add

Patterns(T: with): with
    nil: Pattern(List T, None)
    any: Pattern(T, None)
    bind: Pattern(T, Value T)
    value: T -> Pattern(T, None)
== add
    nil: Pattern(List T, None) ==
        match(l: List T): None == if empty? l then fail else ok
        bind(l: List T): None == none
        pattern(match, bind)

    any: Pattern(T, None) == never
    bind: Pattern(T, Value T) == never
    value(x: T): Pattern(T, None) == never

ConsPackage(T: with, O1: PatternOutputCategory, O2: PatternOutputCategory): with
        cons: (Pattern(T, O1), Pattern(List T, O2)) -> Pattern(List T, Pair(O1, O2))
== add
    cons(p: Pattern(T, O1), r: Pattern(List T, O2)): Pattern(List T, Pair(O1, O2)) == never

matchExample(): () ==
    import from Patterns Integer
    import from ConsPackage(Integer, None, None)
    import from ConsPackage(Integer, Value Integer, Pair(None, None))
    pattern: Pattern(List Integer, Pair(Value Integer, Pair(None, None))) == cons(bind, cons(any, nil))
