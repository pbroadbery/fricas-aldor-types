#include "aldor"
#pile

PointerType: Category == PrimitiveType with
    same?: (%, %) -> Boolean
    default
        import from Pointer
        same?(a: %, b: %): Boolean == a pretend Pointer = b pretend Pointer

AsPointer(T: PointerType): HashType with
    toPointer: T -> %
    fromPointer: % -> T
== add
    Rep == T
    import from Rep

    toPointer(t: T): % == per t
    fromPointer(p: %): T == rep p

    (a: %) = (b: %): Boolean == same?(rep a, rep b)
    hash(a: %): MachineInteger == a pretend Pointer pretend MachineInteger