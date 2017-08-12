#include "aldor"
#include "aldorio"
#pile
#library BITS "bitset.ao"

BitSet: Join(OutputType, PrimitiveType) with
    empty: () -> %
    member?: (MachineInteger, %) -> Boolean
    union: (%, %) -> %
    singleton: MachineInteger -> %
    size: % -> MachineInteger
== add
    Rep == MachineInteger
    import from Rep

    empty(): % == per 0
    member?(n: MachineInteger, s: %): Boolean == bit?(rep s, n)
    union(s1: %, s2: %): % == per (rep s1 \/ rep s2)
    singleton(n: MachineInteger): % == per shift(1, n)
    size(s: %): MachineInteger == length rep s
    (a: %) = (b: %): Boolean == rep(a) = rep(b)

    (o: TextWriter) << (v: %): TextWriter == o << rep v


Pattern(T: with): with
    fields: % -> BitSet
    pattern: (s: BitSet, f: StdPatternOutput T) -> %
    match: (%, T) -> Boolean
    output: % -> StdPatternOutput T
    evaluate: (%, n: MachineInteger, T) -> PrimitiveArray Pointer
    case: (T, %) -> Boolean
== add
    Rep == Cross(fields: BitSet, out: StdPatternOutput T)
    import from Rep
    import from BitSet
    import from StdPatternOutput T

    local unwrap(x: Rep): (BitSet, StdPatternOutput T) == x

    fields(p: %): BitSet ==
        (a, b) := unwrap(rep p)
        a

    output(p: %): StdPatternOutput T ==
        (a, b) := unwrap(rep p)
        b

    pattern(s: BitSet, f: StdPatternOutput T): % == per((s, f)@Rep)
    match(p: %, x: T): Boolean == match(output p, x)

    -- could be used by compiler if we implemented this as a builtin
    evaluate(p: %, nBindings: MachineInteger, x: T): PrimitiveArray Pointer ==
        import from StdPatternOutput T
        o := output p
        not match(o, x) => []
        binder := bind(o, x)
        [binder 0]

    -- local version
    case(v: T, p: %): Boolean ==
        import from MachineInteger
        not match(p, v) => false
        binder := bind(output p, v)
        for i in 0..size fields p - 1 repeat
            stdout << "Binding " << i << newline
            binder i
        true

StdPatternOutput(T: with): with
    output: (match: T -> Boolean, bind: (T, MachineInteger) -> Pointer) -> %
    match: (%, T) -> Boolean
    bind: (%, T) -> MachineInteger -> Pointer
== add
    Rep ==> (T -> (Boolean, MachineInteger -> Pointer))

    output(match: T -> Boolean, bind: (T, MachineInteger) -> Pointer): % ==
        --fn(x: T): (Boolean, MachineInteger -> Pointer) == (match x, (n: MachineInteger): Pointer +-> bind(x, n))
        per ((x: T): (Boolean, MachineInteger -> Pointer) +-> (match x, (n: MachineInteger): Pointer +-> bind(x, n)))

    match(out: %, x: T): Boolean ==
        f0: T -> (Boolean, MachineInteger -> Pointer) == rep out
        (flg: Boolean, fn) := f0 x
        flg

    bind(out: %, x: T): MachineInteger -> Pointer ==
        (flg, fn) := rep(out) x
        fn

Patterns(T: with): with
    any: Pattern(T)
    bind: MachineInteger -> Pattern(T)
    if T has PrimitiveType then value: T -> Pattern(T)
    test: (T -> Boolean) -> Pattern T
== add
    import from StdPatternOutput T

    any: Pattern T ==
        test((x: T): Boolean +-> true)

    if T has PrimitiveType then
        value(desired: T): Pattern T ==
            test((x: T): Boolean +-> x = desired)

    bind(n: MachineInteger): Pattern T ==
        fields: BitSet :=
            qq := singleton n
            stdout << "singleton " << n << " = " << qq << newline
            qq
        match(x: T): Boolean == true
        bind(x: T, n: MachineInteger): Pointer == x pretend Pointer
        pattern(fields, output(match, bind))

    test(fn: T -> Boolean): Pattern T ==
        fields: BitSet := empty()
        match(x: T): Boolean == fn x
        bind(x: T, n: MachineInteger): Pointer == error "test.."
        pattern(fields, output(match, bind))

Patterns2(T: with, X: with): with
    test: (T -> Partial X, Pattern X) -> Pattern T
== add
    test(fn: T -> Partial X, inner: Pattern X): Pattern T ==
        import from Partial X, StdPatternOutput T, StdPatternOutput X
        fields: BitSet := fields inner
        match(x: T): Boolean == not failed? (p := fn x) and match(inner, retract p)
        bind(x: T, n: MachineInteger): Pointer == bind(output inner, retract fn x) n
        pattern(fields inner, output(match, bind))

ListPatterns(T: with): with
    nil: Pattern(List T)
    cons: (Pattern T, Pattern List T) -> Pattern List T
== add
    import from StdPatternOutput T, StdPatternOutput List T
    import from Patterns List T, List T
    import from BitSet

    nil: Pattern List T == test(empty?)

    cons(head: Pattern T, tail: Pattern List T): Pattern List T ==
        import from BitSet
        allFields: BitSet := union(fields head, fields tail)
        stdout << "Head: " << fields head << " tail " << fields tail << " All: " << allFields << newline
        match(x: List T): Boolean == not empty? x and match(head, first x) and match(tail, rest x)
        bind(x: List T, n: MachineInteger): Pointer ==
            stdout << "List bind " << n << " " << (fields head) << newline
            stdout << "lhs fields " << member?(n, fields head) << newline
            member?(n, fields head) =>
                stdout << "Bind lhs" << newline
                bind(output head, first x) n
            bind(output tail, rest x) n
        pattern(allFields, output(match, bind))

