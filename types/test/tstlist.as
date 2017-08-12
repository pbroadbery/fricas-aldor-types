#include "aldor"
#include "aldorio"
#pile

Foo: with == add

LT(X: with): Category == with
    if X has PrimitiveType then
        member?: (X, %) -> Boolean

    default {
        if X has PrimitiveType then {
                    member?(x: X, l: %): Boolean == false
            }
    }


X: with == add
QQ: LT(X) == add

member?$QQ