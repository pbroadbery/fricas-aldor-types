#include "aldor"
#pile

import from SpadTypeLib
inline from SpadTypeLib

Extensible: Category == with
    fields: % -> Fields %

ExtField(T: with, V: Type): with
    name: % -> String
    extField: String -> %
    field: % -> Field V
== add
    Rep == Field V
    import from Rep

    extField(name: String): % == per field name
    field(f: %): Field V == rep f
    name(f: %): String == name rep f

Fields(T: with): with
    value: (%, V: Type, ef: ExtField(T, V)) -> V
    newFields: () -> %
== add
    Rep == DepTable
    import from T, Rep

    value(fields: %, V: Type, ef: ExtField(T, V)): V ==
        import from Field V
        rep(fields).(field ef)

    newFields(): % == per table()
