#include "aldor"
#include "aldorio"
#pile
import from SpadTypeLib
inline from SpadTypeLib

IndexName: OutputType with
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
        X(constructorForm,    "constructorForm")
        X(constructorKind,    "constructorKind")
        X(constructorModemap, "constructorModemap")
        X(parents,            "parents")
        X(operationAlist,     "operationAlist")

    NAMEDECL(id, val) ==> id: %
    NAMEVAL(id, val) ==> id: % == per(-val)
    DECLS ==> NAMES(NAMEDECL)

SymbolKind: PrimitiveType with
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

    VALS
where
    NAMES(X) ==>
        X(domain, "domain")

    NAMEDECL(id, val) ==> id: %
    NAMEVAL(id, val) ==> id: % == newSymbolKind(-val)
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
    import from IndexName, AbSynParser, AbSynUtils, Rep, SExpression
    import from ConstructorModemap
    import from List TForm

    local lookup(axSym: %, id: IndexName): SExpression == get(rep(axSym).file, symbol id)
    local env(axSym: %): Env ==
        import from AxiomLibrary
        env rep(axSym).lib

    local annotate(e: Env, ab: AbSyn): AnnotatedAbSyn ==
        import from AbSynAnnotator
        annotateSym(sym: Symbol): AnnotatedId == newAnnotatedId(e, sym)
        annotate(annotateSym, ab)

    definedSymbol(axSym: %): Symbol == rep(axSym).sym

    newAxiomSymbol(idx: IndexedFile, lib: AxiomLibrary): % ==
        form := parse get(idx, symbol constructorForm)
        per [principalOperator form, idx, form, lib]

    kind(axSym: %): SymbolKind ==
        sx := lookup(axSym, constructorKind)
        valueOf(sym sx)$SymbolKind

    constructorForm(axSym: %): AbSyn ==
        sx := lookup(axSym, constructorForm)
        parse sx

    constructorModemap(axSym: %): ConstructorModemap ==
        sx := lookup(axSym, constructorModemap)
        newConstructorModemap sx

    domainForm(sym: %): TForm ==
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
        [makeParent sx for sx in lookup(sym, parents)]

    local operations(axSym: %): List TForm ==
        import from Fold(List TForm)
        makeOperation(sx: SExpression): List TForm ==
            (name, sx) := (first sx, rest sx)
            [makeSignature(env axSym, sym name, item) for item in sx]
        (append!)/(makeOperation(sx) for sx in lookup(axSym, operationAlist))

    local makeSignature(e: Env, name: Symbol, sx: SExpression): TForm ==
        stdout << "make sig " << name << " --> " << sx << newline
        (type, sx) := (first sx, rest sx)
        (dunno, sx) := (first sx, rest sx)
        cond := if not nil? sx then first sx else nil
        if not nil? dunno then stdout << "found " << name << " --> " << dunno << newline
        newSignature(name, newSyntax(annotate(e, parseSExpression type)), cond)

    local placeholderTForm(sx: SExpression): TForm ==
        sym? sx => newDeclare(sym sx, Type$TForm)
        error("odd placeholder " + toString sx)

    (out: TextWriter) << (axSym: %): TextWriter ==
        import from Symbol
        out << rep(axSym).sym

AxiomLibrary: with
    newLibrary: (Env, String) -> %
    env: % -> Env
    tform: (%, Symbol) -> TForm
== add
    Rep == Record(p: String,
                  env: Env,
                  files: HashTable(Symbol, AxiomSymbol))
    import from Rep
    import from AxiomSymbol, IndexedFile, HashTable(Symbol, AxiomSymbol)

    env(lib: %): Env == rep(lib).env

    newLibrary(e: Env, p: String): % ==
        import from Directory, List FileName, FileName, Symbol
        rec := per [p, e, table()]
        for fname in listDirectory p repeat
            if extension(fname) = "NRLIB" then
                theAxiomSymbol := newAxiomSymbol(newIndexedFile(fname::String + "/index.KAF"), rec)
                rep(rec).files.(definedSymbol theAxiomSymbol) := theAxiomSymbol
        stdout << "Created library. Symbols: " << rep(rec).files << newline
        rec

    local axiomSymbol(lib: %, sym: Symbol): AxiomSymbol == rep(lib).files.sym

    tform(lib: %, sym: Symbol): TForm ==
        import from AbSyn
        axSym: AxiomSymbol := axiomSymbol(lib, sym)
        theKind: SymbolKind := kind axSym
        theKind = domain =>
            domainForm(axSym)
        never

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
    symForm: % -> SExpression
    bodyType: % -> SExpression
    args: % -> List SExpression
== add
    Rep == Record(symForm: SExpression, bodyType: SExpression, args: List SExpression)
    import from Rep, SExpression

    newConstructorModemap(sx: SExpression): % ==
        import from SExpression
        stdout << "MM: Whole " << sx << newline
        stdout << "MM: 1: " << first sx << newline
        mainForm := first sx
        symForm := first mainForm
        symFormType := first rest mainForm
        stdout << "symform " << symForm << newline
        per [symForm, symFormType, []]

    symForm(mm: %): SExpression == rep(mm).symForm
    bodyType(mm: %): SExpression == rep(mm).bodyType
    args(mm: %): List SExpression == rep(mm).args

    (out: TextWriter) << (mm: %): TextWriter == out << "{mm: " << symForm << "}"

testAxiomLib(): () ==
    import from Symbol, TForm
    -- not right, but it'll do.
    env: Env := emptyEnv((ab: AnnotatedAbSyn): TForm +-> Type$TForm)
    lib: AxiomLibrary := newLibrary(env, "/home/pab/Work/fricas/build/src/algebra")
    strType := tform(lib, -"String")
    stdout << strType << newline

    strType := tform(lib, -"List")
    stdout << strType << newline

testAxiomLib()
