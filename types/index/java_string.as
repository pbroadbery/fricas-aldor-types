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
        javaStringToString: JString -> %;
        stringToJavaString: % -> JString;
    from Foreign;

    toJava(x: %): JString == stringToJavaString x
    fromJava(x: JString): % == javaStringToString x

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
