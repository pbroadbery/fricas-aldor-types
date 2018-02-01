#include "aldor"
#include "aldorio"
#pile

JString ==> java_.lang_.String
import JString: with from Foreign Java

extend String: with
    toJava: % -> JString
    fromJava: JString -> %
== add
    import
        Foam: with
            javaStringToString: JString -> Pointer;
            stringToJavaString: Pointer -> JString;
    from Foreign Java "foamj";

    toJava(x: %): JString == stringToJavaString(x pretend Pointer)$Foam
    fromJava(x: JString): % == javaStringToString(x)$Foam pretend %

import from Machine
extend MachineInteger: with
    toJava: % -> SInt;
    fromJava: SInt -> %;
== add
    Rep == SInt
    toJava(i: %): SInt == rep i;
    fromJava(i: SInt): % == per i;

extend Boolean: with
    toJava: % -> Bool;
    fromJava: Bool -> %
== add
    Rep == Bool
    toJava(i: %): Bool == rep i;
    fromJava(i: Bool): % == per i;

import from String

export JList ==> java_.util_.List;
export JIterable ==> java_.lang_.Iterable;

APPLY(id, rhs) ==> { apply: (%, 'id') -> rhs; export from 'id' }

import
    JList: (T: with) -> with
        APPLY(_add, T -> Boolean)
        APPLY(get, MachineInteger -> T)
        APPLY(size, () -> MachineInteger)
        APPLY(set, (MachineInteger, T) -> T)
        APPLY(toString, () -> String)
    JIterable: (T: with) -> with
            APPLY(iterator, () -> Iterator T)
from Foreign Java
import
    JIterable: (T: with) -> with
            APPLY(iterator, () -> Iterator T)
from Foreign Java
import
    Iterator: (T: with) -> with
        APPLY(hasNext, () -> Boolean);
        APPLY(next, () -> T);
from Foreign Java "java.util"
