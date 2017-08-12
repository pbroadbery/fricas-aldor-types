#include "aldor"
#include "aldorio"
#pile

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
