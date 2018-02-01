#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib

import from LibReader

foo(): MachineInteger ==
    c: MachineInteger := 0
    for x in paths("/tmp") repeat
        c := c + #x
    c

#if 0
foo(): String ==
    import from LibReaderX
    p0("/tmp")
#endif
