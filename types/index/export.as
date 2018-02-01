#include "aldor"
#include "aldorio"
#pile

import from SpadTypeLib
inline from SpadTypeLib

export Export to Foreign Java("aldor.elib")
import from SpadTypeLib
inline from SpadTypeLib

export JList ==> java_.util_.List;
export JIterable ==> java_.lang_.Iterable;

APPLY(id, rhs) ==> { apply: (%, 'id') -> rhs; export from 'id' }

import
    ArrayList: (T: with) -> with
        new: MachineInteger -> %
        APPLY(_add, T -> Boolean)
from Foreign Java "java.util"

foo(e: Export): ArrayList Export ==
    import from MachineInteger
    ll := new(1)$ArrayList(Export)
    ll._add(e)
    return ll

