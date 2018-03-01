#include "aldor"
#include "aldorio"
#pile

import from SpadTypeLib
inline from SpadTypeLib

export SExpression to Foreign Java("aldorlib.sexpr")
export Symbol to Foreign Java("aldorlib.sexpr")
export AnnotatedAbSyn to Foreign Java("aldor.typelib")
export AnnotatedId to Foreign Java("aldor.typelib")
export IndexedFile to Foreign Java("aldor.typelib")
export TypePackage to Foreign Java("aldor.typelib")

export TForm to Foreign Java("aldor.typelib")
export Export to Foreign Java("aldor.typelib")
export NamedExport to Foreign Java("aldor.typelib")
export SymbolMeaning to Foreign Java("aldor.typelib")
export AxiomInterface to Foreign Java("aldor.typelib")
export AxiomLibrary to Foreign Java("aldor.typelib")
export Env to Foreign Java("aldor.typelib")
export SymbolDatabase to Foreign Java("aldor.typelib")
export SymbolDatabaseHelper to Foreign Java("aldor.typelib")

export JList ==> java_.util_.List;
export JIterable ==> java_.lang_.Iterable;

APPLY(id, rhs) ==> { apply: (%, 'id') -> rhs; export from 'id' }

import
    JList: (T: with) -> with
        APPLY(_add, T -> Boolean)
        APPLY(get, MachineInteger -> T)
        APPLY(size, () -> MachineInteger)
        APPLY(set, (MachineInteger, T) -> T)
        APPLY(toString, () -> String)
    JIterable: (T: with) -> with
            APPLY(iterator, () -> Iterator T)
from Foreign Java
import
    JIterable: (T: with) -> with
            APPLY(iterator, () -> Iterator T)
from Foreign Java
import
    ArrayList: (T: with) -> with
        new: MachineInteger -> %
        APPLY(_add, T -> Boolean)
    Iterator: (T: with) -> with
        APPLY(hasNext, () -> Boolean);
        APPLY(next, () -> T);
from Foreign Java "java.util"

AxiomInterface: with
    create: SymbolDatabase -> %
    env: % -> Env
    asTForm: (%, String) -> TForm
    allCatParents: (%, TForm) -> ArrayList TForm
    directParents: (%, TForm) -> ArrayList TForm
    directOperations: (%, AnnotatedAbSyn) -> ArrayList NamedExport
    infer: (%, AnnotatedAbSyn) -> TForm
    asTForm: (%, AnnotatedAbSyn) -> TForm
    annotated: (%, String) -> AnnotatedAbSyn
    annotated: (%, AbSyn) -> AnnotatedAbSyn
    library: % -> AxiomLibrary

    allTypes: % -> ArrayList AnnotatedAbSyn

    newApply: (AnnotatedAbSyn, JList AnnotatedAbSyn) -> AnnotatedAbSyn
== add
    Rep == Record(str: String, lib: AxiomLibrary, env: Env)
    import from Rep
    import from Export
    library(iface: %): AxiomLibrary == rep(iface).lib

    create(db: SymbolDatabase): % ==
        basicTypeSystem: TypeSystem := typeSystem()$SimpleTypeSystem

        emptyEnv: Env :=
            import from TypePackage
            sat: FnSatisfier := (satisfier$SimpleSatisfier)::FnSatisfier
            envInferFn(ab: AnnotatedAbSyn): TForm == infer(sat, ab)
            emptyEnv(envInferFn)$Env

        --[paths(p)$LibReader]$List(String)
        lib: AxiomLibrary := newLibrary(basicTypeSystem, emptyEnv, db)
        libEnv: Env := env lib
        per [name db, lib, libEnv]

    env(iface: %): Env ==
        rep(iface).env

    asTForm(iface: %, s: String): TForm ==
        import from SExpression, String, AbSyn
        asTForm(iface, annotated(iface, parseSExpression fromString s))

    asTForm(iface: %, ab: AnnotatedAbSyn): TForm ==
        import from TypePackage
        newSyntax(typeSystem()$SimpleTypeSystem, canonicalise ab)

    allCatParents(iface: %, tf: TForm): ArrayList TForm ==
        exports: List Export := allCatParents(tf)$TypePackage
        arrayList(type e for e in exports)

    directParents(iface: %, tf0: TForm): ArrayList TForm ==
        import from SExpression
        import from Symbol, TfSignature, SimpleSatisfier, TfGeneral
        local isParent(e: Export): Boolean ==
            import from SExpression
            signature? type e => false
            type e = tf => false
            true
        tf: TForm := if satisfiesDomain? tf0 then tf := type(tf0::TfGeneral) else tf0
        --tf := tf0
        exports: List Export := directCatParents(tf)
        arrayList(type e for e in exports | isParent(e))

    directOperations(iface: %, ab: AnnotatedAbSyn): ArrayList NamedExport ==
        import from Symbol, TfSignature, NamedExport, TfThird, List Export, SubstitutionPackage
        tf: TForm := infer(iface, ab)
        if third? tf then tf := cat(tf::TfThird)
        osubst := substToOriginal(iface, ab)
        symes: List NamedExport := [namedExport(newExport(type e, subst(original e, osubst))) for e in directCatParents(tf) | signature? type e]
        arrayList symes

    local substToOriginal(iface: %, ab: AnnotatedAbSyn): AbSub ==
        import from TfMap, AxiomSymbol, AxiomLibrary, Partial TForm
        import from List TForm, List AnnotatedAbSyn, MachineInteger
        not apply? ab or applyArgCount ab = 0 => emptySubst()
        aid: AnnotatedId := principalOperator ab
        cform: AnnotatedAbSyn := constructorForm(symbol(library iface, id aid))
        mapTf: TForm := retract tform(library iface, id aid)
        formalSymbol(tfArg: TForm): Symbol ==
            import from TfDeclare
            sym(tfArg::TfDeclare)
        [(formalSymbol mapArg, cformArg) for mapArg in args(mapTf::TfMap) for cformArg in applyArguments cform]


    infer(iface: %, ab: AnnotatedAbSyn): TForm == infer(env(iface), ab)

    annotated(iface: %, text: String): AnnotatedAbSyn ==
        import from SExpression, AbSyn
        annotated(iface, parseSExpression fromString text)

    annotated(iface: %, ab: AbSyn): AnnotatedAbSyn ==
        import from AbSynAnnotator
        annotateSym(id: Symbol): AnnotatedId == newAnnotatedId(env iface, id)
        annotate(annotateSym, ab)

    newApply(op: AnnotatedAbSyn, l: JList AnnotatedAbSyn): AnnotatedAbSyn ==
        import from MachineInteger
        ll: List AnnotatedAbSyn := [l.get(i) for i in 0.. (l.size()) -1]
        newApply(op, ll)

    allTypes(iface: %): ArrayList AnnotatedAbSyn ==
        import from AxiomSymbol, List Symbol
        arrayList(constructorForm symbol(library iface, sym) for sym in ids library iface)

    local arrayList(list: List NamedExport): ArrayList NamedExport ==
        import from MachineInteger
        al: ArrayList NamedExport := new(# list)
        for exp in list repeat
            al._add(exp)
        return al

    local arrayList(list: List SymbolMeaning): ArrayList SymbolMeaning ==
        import from MachineInteger
        al: ArrayList SymbolMeaning := new(# list)
        for exp in list repeat
            al._add(exp)
        return al

    local arrayList(gg: Generator SymbolMeaning): ArrayList SymbolMeaning ==
        import from MachineInteger
        al: ArrayList SymbolMeaning := new(10)
        for exp in gg repeat
            al._add(exp)
        return al

    local arrayList(list: Generator TForm): ArrayList TForm ==
        import from MachineInteger
        al: ArrayList TForm := new(10)
        for exp in list repeat
            al._add(exp)
        return al

    local arrayList(list: Generator AnnotatedAbSyn): ArrayList AnnotatedAbSyn ==
        import from MachineInteger
        al: ArrayList AnnotatedAbSyn := new(10)
        for exp in list repeat
            al._add(exp)
        return al

NamedExport: SExpressionOutputType with
    namedExport: Export -> %
    name: % -> Symbol
    type: % -> TForm
    --condition: % -> SExpression
    original: % -> TForm
== add
    Rep == Export
    import from Rep, TfSignature, SymbolMeaning

    namedExport(e: Export): % ==
        not signature? type e => error "expected a signature"
        per e

    local signature(ne: %): TfSignature == type(rep(ne))::TfSignature
    local originalSignature(ne: %): TfSignature == original(rep(ne))::TfSignature
    name(ne: %): Symbol == name symbolMeaning signature ne
    type(ne: %): TForm == type symbolMeaning signature ne
    original(ne: %): TForm == type symbolMeaning originalSignature ne

    sexpression(ne: %): SExpression ==
        import from Symbol, TForm
        [sexpr(-"Named"), sexpr name ne, sexpression type ne]

SymbolDatabaseHelper: with
    nrlib: String -> SymbolDatabase
== add
    nrlib(p: String): SymbolDatabase ==
        import from FileName
        nrlib(p, (): List FileName +-> [f::FileName for f in paths(p)$LibReader | extension(f::FileName) = "NRLIB"])
