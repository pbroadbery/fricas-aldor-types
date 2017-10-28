#include "aldor"
#include "aldorio"
#pile

Java(headers:Literal): ForeignLanguage == add
string(x: Literal): Literal == x

export
    createJ: List String -> AldorTypePackage
to Foreign Java("aldor.types.AldorTypePackage")

createJ(l: List String): AldorTypePackage ==
    create l

AldorTypePackage: with
    create: List String -> %
    isValid: (%, String) -> Boolean
    exports: (%, String) -> List String
== add
    create(l: List String): % == never
    isValid(pkg: %, s: String): Boolean == false
    exports(pkg: %, s: String): List String == []


