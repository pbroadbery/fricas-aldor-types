#include "aldor"
#include "algebra"
#include "aldorio"
#pile

DualNumber(R: Ring): Join(Ring, Algebra Integer) with
    dual: (R, R) -> %
    eps: %
    real: % -> R
    other: % -> R
== add
    Rep ==> Record(a: R, b: R)
    import from Rep, R

    commutative?: Boolean == true
    characteristic: Integer == characteristic$R

    dual(a: R, b: R): % == per [a, b]

    1: % == per [1, 0]
    0: % == per [0, 0]
    eps: % == per [0, 1]

    real(x: %): R == rep(x).a
    other(x: %): R == rep(x).b

    -(x: %): % ==
        (xa, xb) := explode rep x
        per [-xa, -xb]

    (x: %) + (y: %): % ==
            (xa, xb) := explode rep x
            (ya, yb) := explode rep y
            per [xa+ya, xb + xa]

    (x: %) * (y: %): % ==
         (xa, xb) := explode rep x
         (ya, yb) := explode rep y
         per [xa*ya, xa*yb + xb*ya]

    (x: %) = (y: %): Boolean ==
         (xa, xb) := explode rep x
         (ya, yb) := explode rep y
         xa = ya and xb = yb


    extree(x: %): ExpressionTree ==
        import from List ExpressionTree
        ExpressionTreePlus [extree real x, extree other x]
