#include "aldor"
--#include "aldorio"
#pile
import from SpadTypeLib
inline from SpadTypeLib

export SExpression to Foreign Java("aldorlib.sexpr")
export Symbol to Foreign Java("aldorlib.sexpr")
export AnnotatedAbSyn to Foreign Java("aldor.typelib")
export AnnotatedId to Foreign Java("aldor.typelib")
export IndexedFile to Foreign Java("aldor.typelib")

export TForm to Foreign Java("aldor.typelib")
export Export to Foreign Java("aldor.typelib")
export AxiomInterface to Foreign Java("aldor.typelib")
export Env to Foreign Java("aldor.typelib")

AxiomInterface: with
    create: String -> %
    env: % -> Env
    asTForm: (%, String) -> TForm
== add
    Rep == Record(str: String, lib: AxiomLibrary, env: Env)
    import from Rep

    create(p: String): % ==
        basicTypeSystem: TypeSystem := typeSystem()$SimpleTypeSystem

        emptyEnv: Env :=
            import from TypePackage
            sat: FnSatisfier := (satisfier$SimpleSatisfier)::FnSatisfier
            envInferFn(ab: AnnotatedAbSyn): TForm == infer(sat, ab)
            emptyEnv(envInferFn)$Env

        lib: AxiomLibrary := newLibrary(basicTypeSystem, emptyEnv, p, [paths(p)$LibReader]$List(String))
        libEnv: Env := env lib
        per [p, lib, libEnv]

    env(iface: %): Env ==
        rep(iface).env


    local annotate(env: Env)(ab: AbSyn): AnnotatedAbSyn ==
        import from AbSynAnnotator
        annotateSym(id: Symbol): AnnotatedId == newAnnotatedId(env, id)
        annotate(annotateSym, ab)

    asTForm(iface: %, s: String): TForm ==
        import from SExpression, String, AbSyn
        tf := newSyntax(typeSystem()$SimpleTypeSystem,
                        (annotate env iface) parseSExpression fromString "(Map String String)")

