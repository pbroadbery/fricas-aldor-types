#include "aldor"
#include "aldorio"
#library PAT "pattern2.ao"
#pile

import from PAT
inline from PAT

matchExample(x: List Integer): () ==
    import from Patterns Integer
    import from ListPatterns(Integer)
    import from MachineInteger
    pattern: Pattern List Integer == cons(bind 0, cons(any, nil))
    val := evaluate(pattern, 1, x)


matchExample2(x: Integer): () ==
    import from Patterns Integer
    import from MachineInteger
    pattern: Pattern Integer == bind 0
    val := evaluate(pattern, 1, x)

Binder: with
    binder: () -> %
    matcher: (%, T: with) -> PatternBox T
    wrap: (%, T: with) -> PatternBox T
== add
    Rep == Record(n: MachineInteger)
    import from Rep, MachineInteger

    binder(): % == per [0]

    matcher(b: %, T: with): PatternBox T ==
        idx := rep(b).n
        rep(b).n := idx + 1
        patternBox idx

    wrap(b: %, T: with): PatternBox T == matcher(b, T)


PatternBox(T: with): with
    patternBox: MachineInteger -> %
    unwrap: % -> T
    bind: % -> Pattern T
== add
    Rep == Union(n: MachineInteger, val: T)
    import from Rep
    import from StdPatternOutput T

    patternBox(n: MachineInteger): % == per [n]
    unwrap(box: %): T == rep(box).val

    bind(box: %): Pattern T ==
        fields: BitSet := singleton rep(box).n
        match(x: T): Boolean == true

        bind(x: T, n: MachineInteger): Pointer ==
            rep(box).val := x
            x pretend Pointer
        pattern(fields, output(match, bind))

test() : () ==
    import from ListPatterns(Integer)
    import from Patterns List Integer
    import from Pattern List Integer
    import from Patterns Integer
    import from ListPatterns Integer
    import from Integer
    import from List Integer
    import from PatternBox Integer

    x := [1,2,3]
    --qq: Pattern Integer := never

    stdout << "test starts" << newline
    b: Binder := binder()
    select x in
        nil => stdout << "empty" << newline
        cons(bind(h := wrap(b, Integer)), cons(bind(two := wrap(b, Integer)), any)) => stdout << unwrap(h) << " " << unwrap(two) << newline
        never


AbSyn: with
    lit: Pattern String -> Pattern %
    pair: Pattern List % -> Pattern %
    lit: String -> %
    pair: (%, %) -> %
== add
    Rep == Union(LIT: String, PAIR: List %)
    import from Rep
    import from Patterns String, Patterns2(%, String), Patterns2(%, List %), Partial String, Partial List %

    lit(s: String): % == per [s]
    pair(a: %, b: %): % == per [[a, b]]
    lit(p: Pattern String): Pattern % ==
        test((a: %): Partial String +-> if rep(a) case LIT then [rep(a).LIT] else failed, p)

    pair(p: Pattern List %): Pattern % ==
        test((a: %): Partial List % +-> if rep(a) case PAIR then [rep(a).PAIR] else failed, p)


test()

-----------

Match(T: Type): with
    match: T -> %
== add
    match(x: T): % == never

Ab: with
    parse: String -> %
    lit: Pattern String -> Pattern %
    pair: (Pattern String, Pattern Integer) -> Pattern %
== add
    parse(txt: String): % == never
    lit(s: Pattern String): Pattern % == never
    pair(lhs: Pattern String, rhs: Pattern Integer): Pattern % == never

Pattern(T: Type): with
    case: (Match T, Pattern T) -> Boolean
== add
    case(m: Match T, p: Pattern T): Boolean == never

Patterns: with
    any: (T: Type) -> Pattern T
== add
    any(T: Type): Pattern T == never

trial(): () ==
    import from Match Ab
    x: Ab := parse("hello")
    select match(x) in
        lit(foo := any(String)) => value(foo)
        pair(lhs := any(String), rhs := any(Integer)) => value(lhs)
