#include "aldor"
#include "aldorio"
#pile
import from SpadTypeLib
inline from SpadTypeLib

ConstLibrary: OutputType with
    constLibrary: List SymbolMeaning -> %
    lookup: % -> Symbol -> Partial TForm
== add
    Rep == HashTable(Symbol, TForm)
    import from Rep

    constLibrary(symes: List SymbolMeaning): % ==
        import from SymbolMeaning
        tbl := [(name syme, type syme) for syme in symes]
        per tbl

    lookup(l: %)(sym: Symbol): Partial TForm == find(sym, rep l)

    (out: TextWriter) << (lib: %): TextWriter == out << "{lib}"

BasicLibrary: with
    basicLibrary: (TypeSystem, Env) -> %
    imports: % -> List SymbolMeaning
== add
    Rep == List SymbolMeaning
    import from Rep
    default thisEnv: Env
    default ts: TypeSystem

    import from Symbol, AnnotatedAbSyn, AbSyn, SExpression
    import from List TForm, List AnnotatedAbSyn

    local type(ts, thisEnv): TForm == Type$TForm

    local tuple(ts, thisEnv): TForm ==
       lhs: TForm := newDeclare(-"|#1|", Type$TForm)
       rhs: TForm := bind(newCategory [], annotate(thisEnv, parseSExpression fromString "(Tuple |#1|)"))
       newMap(lhs, rhs)

    local record(ts, thisEnv): TForm ==
       lhs: TForm := newDeclare(-"#1", newSyntax(ts, annotate(thisEnv, parseSExpression fromString "Tuple Type")))
       rhs: TForm := bind(newCategory [], annotate(thisEnv, parseSExpression fromString "(Record |#1|)"))
       newMap(lhs, rhs)

    local cross(ts, thisEnv): TForm ==
       lhs: TForm := newDeclare(-"#1", newSyntax(ts, annotate(thisEnv, parseSExpression fromString "Tuple Type")))
       rhs: TForm := bind(newCategory [], annotate(thisEnv, parseSExpression fromString "(Cross |#1|)"))
       newMap(lhs, rhs)

    basicLibrary(ts: TypeSystem, parentEnv: Env): % ==
        import from SymbolMeaning
        tbl: HashTable(Symbol, TForm) := table()
        localEnv := newEnv((s: Symbol): Partial TForm +-> find(s, tbl), parentEnv)
        tbl.(-"Tuple") := tuple(ts, localEnv)
        tbl.(-"Record") := record(ts, localEnv)
        tbl.(-"Cross") := cross(ts, localEnv)
        tbl.(-"Type") := type(ts, localEnv)
        per [newSymbolMeaning(k, v) for (k, v) in tbl]

    local annotate(e: Env, ab: AbSyn): AnnotatedAbSyn ==
        import from AbSynAnnotator
        annotateSym(sym: Symbol): AnnotatedId == newAnnotatedId(e, sym)
        annotate(annotateSym, ab)

    imports(l: %): List SymbolMeaning == rep l
