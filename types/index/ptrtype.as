#include "aldor"
#pile

PointerType: Category == PrimitiveType with
    same?: (%, %) -> Boolean
    default
        import from Pointer
        same?(a: %, b: %): Boolean == a pretend Pointer = b pretend Pointer
