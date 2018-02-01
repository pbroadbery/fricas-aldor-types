#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib


testIndex(): () ==
    import from Symbol, IndexedFile, SExpression, MachineInteger
    f := new("/home/pab/Work/fricas/build/src/algebra/A1AGG-.NRLIB/index.KAF")
    stdout << get(f, -"abbreviation", 1) << newline

testIndex2(): () ==
    import from Symbol, IndexedFile, SExpression, MachineInteger
    f := new("/home/pab/Work/fricas/opt/lib/fricas/target/x86__64-unknown-linux/algebra/browse.daase")
    stdout << get(f, -"Integer", 1) << newline

testIndex()
testIndex2()
