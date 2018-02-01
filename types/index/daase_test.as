#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib


test0(): () ==
    import from List Symbol, Symbol, LibAttribute, SExpression
    import from Assert SExpression
    dir: String := "/home/pab/Work/fricas/opt/lib/fricas/target/x86__64-unknown-linux/algebra"
    interp: IndexedFile := new(dir + "/interp.daase")
    browser: IndexedFile := new(dir + "/browse.daase")
    daase: AxiomDaaseFiles := new(interp, browser)

    --stdout << "Symbols are: " << symbols daase << newline
    stdout << "Abbrev Integer " << get(daase, -"Integer", libAttrAbbreviation) << newline
    stdout << "Abbrev Integer " << get(daase, -"Polynomial", libAttrAbbreviation) << newline
    assertEquals(sexpr(-"INT"), get(daase, -"Integer", libAttrAbbreviation))
    assertEquals(sexpr(-"POLY"), get(daase, -"Polynomial", libAttrAbbreviation))

test0()
