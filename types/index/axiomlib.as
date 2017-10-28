#include "aldor"
#include "aldorio"
#pile
import from SpadTypeLib
inline from SpadTypeLib

import from String

LibAttribute: OutputType with
    DECLS
    symbol: % -> Symbol
== add
    Rep == Symbol
    import from Rep
    symbol(n: %): Symbol == rep n
    NAMES(NAMEVAL)
    (out: TextWriter) << (n: %): TextWriter == out << rep n
where
    NAMES(X) ==>
        X(libAttrAbbreviation,       "abbreviation")
        X(libAttrConstructorForm,    "constructorForm")
        X(libAttrConstructorKind,    "constructorKind")
        X(libAttrConstructorModemap, "constructorModemap")
        X(libAttrOperationAlist,     "operationAlist")
        X(libAttrParents,            "parents")

    NAMEDECL(id, val) ==> id: %
    NAMEVAL(id, val) ==> id: % == per(-val)
    DECLS ==> NAMES(NAMEDECL)

SymbolKind: Join(PrimitiveType, OutputType) with
    name: % -> Symbol
    valueOf: Symbol -> %
    DECLS
== add
    Rep == Symbol
    import from Rep

    name(k: %): Symbol == rep k
    valueOf(sym: Symbol): % ==
        -- Should check for unknown symbols
        newSymbolKind sym

    local newSymbolKind(sym: Symbol): % == per sym

    (a: %) = (b: %): Boolean == rep(a) = rep(b)
    (out: TextWriter) << (a: %): TextWriter == out << rep(a)
    VALS
where
    NAMES(X) ==>
        X(domain, "domain")

    NAMEDECL(id, val) ==> id: %
    NAMEVAL(id, val) ==>
        id: % == newSymbolKind(-val)
    DECLS ==> NAMES(NAMEDECL)
    VALS ==> NAMES(NAMEVAL)

AxiomSymbol: OutputType with
    newAxiomSymbol: (IndexedFile, AxiomLibrary) -> %
    definedSymbol: % -> Symbol
    kind: % -> SymbolKind
    domainForm: % -> TForm
    constructorForm: % -> AbSyn
    constructorModemap: % -> ConstructorModemap
== add
    Rep == Record(sym: Symbol, file: IndexedFile, constructorForm: AbSyn, lib: AxiomLibrary)
    import from Rep
    import from LibAttribute, AbSynParser, AbSynUtils, Rep, SExpression
    import from ConstructorModemap
    import from List TForm

    local lookup(axSym: %, id: LibAttribute): SExpression ==
        get(rep(axSym).file, symbol id)

    local env(axSym: %): Env ==
        import from AxiomLibrary
        env rep(axSym).lib

    local annotate(e: Env, ab: AbSyn): AnnotatedAbSyn ==
        import from AbSynAnnotator
        annotateSym(sym: Symbol): AnnotatedId == newAnnotatedId(e, sym)
        annotate(annotateSym, ab)

    definedSymbol(axSym: %): Symbol == rep(axSym).sym

    newAxiomSymbol(idx: IndexedFile, lib: AxiomLibrary): % ==
        form := parse get(idx, symbol libAttrConstructorForm)
        per [principalOperator form, idx, form, lib]

    kind(axSym: %): SymbolKind ==
        sx := lookup(axSym, libAttrConstructorKind)
        valueOf(sym sx)$SymbolKind

    constructorForm(axSym: %): AbSyn ==
        sx := lookup(axSym, libAttrConstructorForm)
        parse sx

    constructorModemap(axSym: %): ConstructorModemap ==
        sx := lookup(axSym, libAttrConstructorModemap)
        newConstructorModemap sx

    domainForm(sym: %): TForm ==
        stdout << "(DomainForm " << sym << newline
        df := domainForm1 sym
        stdout << " DomainForm " << sym << " = " << df << ")" << newline
        df

    domainForm1(sym: %): TForm ==
        modemap: ConstructorModemap := constructorModemap sym
        form := symForm modemap
        if nil? rest form then
            boundCategory(sym)
        else
            newMap([placeholderTForm id for id in rest form], [boundCategory sym])

    local boundCategory(sym: %): TForm ==
        bind(newCategory(append!(parents sym, operations sym)),
             annotate(env sym, parseSExpression symForm constructorModemap sym))

    local parents(sym: %): List TForm ==
        makeParent(sx: SExpression): TForm ==
            import from Symbol
            lhs := first sx
            cond := rest sx
            lhsTf: TForm := newSyntax(annotate(env sym, parseSExpression lhs))
            if sexpr(-"T") = cond then lhsTf
            else newIf(cond, lhsTf)
        [makeParent sx for sx in lookup(sym, libAttrParents)]

    local operations(axSym: %): List TForm ==
        import from Fold(List TForm)
        makeOperation(sx: SExpression): List TForm ==
            (name, sx) := (first sx, rest sx)
            [makeSignature(env axSym, sym name, item) for item in sx]
        (append!)/(makeOperation(sx) for sx in lookup(axSym, libAttrOperationAlist))

    local makeSignature(e: Env, name: Symbol, sx: SExpression): TForm ==
        stdout << "make sig: " << sx << newline
        safeFirst(sx: SExpression): SExpression == if nil? sx then nil else first sx
        safeRest(sx: SExpression): SExpression == if nil? sx then nil else rest sx

        (sigSx, sx) := (first sx, rest sx)
        (slot, sx) := (first sx, rest sx)
        (cond, sx) := (safeFirst sx, safeRest sx)
        (const, sx) := (safeFirst sx, safeRest sx)

        types := [newSyntax(annotate(e, parseSExpression tsx)) for tsx in sigSx]
        stdout << "types are: " << types << newline
        tf := if not nil? const then first types else newMap(newMulti(rest types), first types)

        newSignature(name, tf, cond)

    local placeholderTForm(sx: SExpression): TForm ==
        sym? sx => newDeclare(sym sx, Type$TForm)
        error("odd placeholder " + toString sx)

    (out: TextWriter) << (axSym: %): TextWriter ==
        import from Symbol
        out << rep(axSym).sym

AxiomLibrary: with
    newLibrary: (Env, String) -> %
    newLibrary: (Env, List(HashTable(Symbol, SExpression))) -> %
    env: % -> Env
    tform: (%, Symbol) -> Partial TForm
== add
    Rep == Record(p: String,
                  env: Env,
                  files: HashTable(Symbol, AxiomSymbol))
    import from Rep
    import from AxiomSymbol, IndexedFile, HashTable(Symbol, AxiomSymbol)

    env(lib: %): Env ==
        lookup(sym: Symbol): Partial TForm == tform(lib, sym)
        newEnv(lookup, rep(lib).env)

    newLibrary(e: Env, l: List(HashTable(Symbol, SExpression))): % ==
        rec := per ["testlib", e, table()]
        for sym in (makeSymbol(rec, tbl) for tbl in l) repeat
            import from Symbol
            stdout << "AxiomLibrary::newLib: " << sym << definedSymbol sym << newline
            rep(rec).files.(definedSymbol sym) := sym
        rec


    local makeSymbol(lib: %, tbl: HashTable(Symbol, SExpression)): AxiomSymbol ==
        import from Symbol, SExpression, LibAttribute
        idxFile: IndexedFile := newIndexedFile(name sym tbl.(symbol libAttrAbbreviation), tbl)
        newAxiomSymbol(idxFile, lib)

    newLibrary(e: Env, p: String): % ==
        import from Directory, List FileName, FileName, Symbol
        rec := per [p, e, table()]
        for fname in listDirectory p repeat
            stdout << "fname: " << fname << newline
            if extension(fname) = "NRLIB" then
                theAxiomSymbol := newAxiomSymbol(newIndexedFile(fname::String + "/index.KAF"), rec)
                rep(rec).files.(definedSymbol theAxiomSymbol) := theAxiomSymbol
                stdout << "Defining " << definedSymbol theAxiomSymbol << " " << fname << newline
        stdout << "Created library. Name: " << p << newline
        rec

    local axiomSymbol(lib: %, sym: Symbol): Partial AxiomSymbol ==
        import from Partial AxiomSymbol
        r := find(sym, rep(lib).files)
        if failed? r then
            stdout << "Failed to find " << sym << " in " << rep(lib).p << newline
        r

    tform(lib: %, sym: Symbol): Partial TForm ==
        import from AbSyn
        axSym: Partial AxiomSymbol := axiomSymbol(lib, sym)
        stdout << "Sym: " << sym << " --> " << axSym << newline
        failed? axSym => failed
        theKind: SymbolKind := kind retract axSym
        stdout << "kind: " << theKind << newline
        theKind = domain =>
            [domainForm(retract axSym)]
        failed

Scope: with
    tform: (%, AbSyn) -> Partial TForm
== add
    Rep == Record(f: Symbol -> Partial TForm)
    import from Rep
    tform(scope: %, ab: AbSyn): Partial TForm ==
        ff: Symbol -> Partial TForm := rep(scope).f
        id? ab => ff(idSymbol ab)
        apply? ab =>
            lhs := tform(scope, applyOperator ab)
            -- subst goes here...
        never

ConstructorModemap: OutputType with
    newConstructorModemap: SExpression -> %
    newConstructorModemap: SExpression -> %
    symForm: % -> SExpression
    bodyType: % -> SExpression
    args: % -> List SExpression
== add
    Rep == Record(symForm: SExpression, bodyType: SExpression, args: List SExpression)
    import from Rep, SExpression

    newConstructorModemap(sx: SExpression): % ==
        import from SExpression
        mainForm := first sx
        symForm := first mainForm
        symFormType := first rest mainForm
        per [symForm, symFormType, []]

    symForm(mm: %): SExpression == rep(mm).symForm
    bodyType(mm: %): SExpression == rep(mm).bodyType
    args(mm: %): List SExpression == rep(mm).args

    (out: TextWriter) << (mm: %): TextWriter == out << "{mm: " << symForm << "}"

testAxiomLib(): () ==
    import from Symbol, TForm, Partial TForm
    -- not right, but it'll do.
    env: Env := emptyEnv((ab: AnnotatedAbSyn): TForm +-> Type$TForm)
    lib: AxiomLibrary := newLibrary(env, "/home/pab/Work/fricas/build/src/algebra")
    strType := tform(lib, -"String")
    stdout << strType << newline

    strType := tform(lib, -"List")
    stdout << strType << newline

--testAxiomLib()
