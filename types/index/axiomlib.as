#include "aldor"
#include "aldorio"
#pile
import from SpadTypeLib
inline from SpadTypeLib

import from String

LibAttribute: OutputType with
    DECLS
    PrimitiveType
    symbol: % -> Symbol
    file: % -> 'interp,browse'
    index: % -> MachineInteger
    export from 'interp,browse'
== add
    Rep == Record(sym: Symbol, file: 'interp,browse', index: MachineInteger)
    import from Rep

    (a: %) = (b: %): Boolean == symbol a = symbol b

    symbol(n: %): Symbol == rep(n).sym
    file(n: %): 'interp,browse' == rep(n).file
    index(n: %): MachineInteger == rep(n).index

    NAMES(NAMEVAL)
    (out: TextWriter) << (n: %): TextWriter == out << symbol n
where
    NAMES(X) ==>
        X(libAttrAbbreviation,       "abbreviation", interp, 6)
        X(libAttrConstructorForm,    "constructorForm", browse, 1)
        X(libAttrConstructorKind,    "constructorKind", interp, 8)
        X(libAttrConstructorModemap, "constructorModemap", interp, 1)
        X(libAttrConstructorCategory,"constructorCategory", interp, 4)
        X(libAttrOperationAlist,     "operationAlist", interp, 0)
        X(libAttrParents,            "parents", interp, -1)

    NAMEDECL(id, val, file, index) ==> id: %
    NAMEVAL(id, val, file, index) ==> id: % == per[(-val), file, index]
    DECLS ==> NAMES(NAMEDECL)

NRLibFile: with
    new: IndexedFile -> %
    get: (%, LibAttribute) -> SExpression
== add
    Rep == IndexedFile
    import from Rep, MachineInteger

    new(file: IndexedFile): % == per file

    get(nrlib: %, attr: LibAttribute): SExpression ==
        get(rep nrlib, symbol attr, 2)

-- format of an entry in interp.daase:
--  (constructor-name
--    operationalist
--    constructormodemap
--    modemaps            -- this should not be needed. eliminate it.
--    object              -- the name of the object file to load for this con.
--    constructorcategory -- note that this info is the cadar of the
--         constructormodemap for domains and packages so it is stored
--         as NIL for them. it is valid for categories.
--    niladic             -- t or nil directly
--    abbreviation        -- kept directly
--    cosig               -- kept directly
--    constructorkind     -- kept directly
--    defaultdomain       -- a short list, for %i
--    ancestors           -- used to compute new category updates

AxiomDaaseFiles: with
    symbols: % -> List Symbol
    new: (IndexedFile, IndexedFile) -> %
    get: (%, Symbol, LibAttribute) -> SExpression
== add
    Rep == Record(interp: IndexedFile, browse: IndexedFile)
    import from Rep, IndexedFile

    symbols(daase: %): List Symbol == keys(rep(daase).interp)

    new(interpDaase: IndexedFile, browseDaase: IndexedFile): % == per [interpDaase, browseDaase]

    get(daase: %, sym: Symbol, attr: LibAttribute): SExpression ==
        val: SExpression := get(daaseFile(daase, attr), sym, index attr)
        if attr = libAttrConstructorCategory and val = nil then
            never
        val

    local daaseFile(daase: %, attr: LibAttribute): IndexedFile ==
        if file attr = interp then rep(daase).interp else rep(daase).browse

NrLibFiles: with
    new: (() -> List FileName) -> %
    get: (%, Symbol, LibAttribute) -> SExpression
    symbols: % -> List Symbol
== add
    FileMaybe == Union(name: FileName, file: IndexedFile)
    Rep == HashTable(Symbol, FileMaybe)
    import from Rep, FileMaybe, 'none'

    symbols(files: %): List Symbol == [k for (k, v) in rep(files)]

    new(ls: () -> List FileName): % ==
        import from List FileName
        local isNrLib(fname: FileName): Boolean == extension(fname) = "NRLIB"
        per [(readAbbrev fname, [fname]) for fname in ls() | isNrLib(fname)]

    get(files: %, sym: Symbol, libAttr: LibAttribute): SExpression ==
        import from FileName, MachineInteger
        fileMaybe: FileMaybe := rep(files).sym
        if fileMaybe case name then
            indexedFile: IndexedFile := new(fileMaybe.name::String)
        else
            indexedFile := fileMaybe.file
        get(indexedFile, symbol libAttr, 1)

    local readAbbrev(fn: FileName): Symbol ==
        import from LibAttribute, MachineInteger
        theFile: String := fn::String
        indexedFile: IndexedFile := new theFile
        sx : SExpression:= get(indexedFile, symbol libAttrAbbreviation, 1)
        return sym sx

SymbolDatabase: with
    name: % -> String
    symbols: % -> List Symbol
    get: (%, Symbol) -> LibAttribute -> SExpression
    nrlib: (String, () -> List FileName) -> %
    nrlib: (String, List HashTable(Symbol, SExpression)) -> %
    daases: String -> %
== add
    Rep == Record(name: String, symbols: List Symbol, getter: (Symbol, LibAttribute) -> SExpression)
    import from Rep

    name(db: %): String == rep(db).name

    symbols(db: %): List Symbol == rep(db).symbols

    get(db: %, sym: Symbol)(attr: LibAttribute): SExpression == (rep(db).getter)(sym, attr)

    nrlib(path: String, ls: () -> List FileName): % ==
        nrlibFiles: NrLibFiles := new(ls)$NrLibFiles
        per [path, symbols(nrlibFiles),
              (sym: Symbol, attr: LibAttribute): SExpression +-> get(nrlibFiles, sym, attr)]


    nrlib(path: String, tbls: List HashTable(Symbol, SExpression)): % ==
        import from IndexedFile, LibAttribute, SExpression, HashTable(Symbol, SExpression)
        local constructor(tbl: HashTable(Symbol, SExpression)): Symbol ==
            cform: SExpression := first rest tbl.(symbol libAttrConstructorForm)
            while not sym? cform repeat cform := first cform
            sym cform
        tblForConstructor: HashTable(Symbol, HashTable(Symbol, SExpression)) == [(constructor(tbl), tbl) for tbl in tbls]
        get(sym: Symbol, attr: LibAttribute): SExpression == first rest tblForConstructor.sym.(symbol attr)
        stdout << "Created library " << [k for (k, v) in tblForConstructor] << newline
        per [path, [k for (k, v) in tblForConstructor], get]

    daases(path: String): % ==
        import from IndexedFile
        daaseFiles: AxiomDaaseFiles := new(new(path + "/interp.daase"), new(path + "/browse.daase"))
        per [path,
                symbols daaseFiles,
                (sym: Symbol, attr: LibAttribute): SExpression +-> get(daaseFiles, sym, attr)]

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
        X(category, "category")
        X(package, "package")

    NAMEDECL(id, val) ==> id: %
    NAMEVAL(id, val) ==>
        id: % == newSymbolKind(-val)
    DECLS ==> NAMES(NAMEDECL)
    VALS ==> NAMES(NAMEVAL)

AxiomSymbol: OutputType with
    newAxiomSymbol: (Symbol, AxiomLibrary) -> %
    definedSymbol: % -> Symbol
    kind: % -> SymbolKind
    domainForm: % -> TForm
    categoryForm: % -> TForm
    constructorModemap: % -> ConstructorModemap
    constructorForm: % -> AnnotatedAbSyn
== add
    Rep == Record(sym: Symbol, lib: AxiomLibrary)
    import from Rep
    import from LibAttribute, AbSyn, AbSynParser, Rep, SExpression
    import from ConstructorModemap
    import from List TForm
    import from MachineInteger
    import from TypePackage

    local vars: Array Symbol := [-"#1",-"#2",-"#3",-"#4",-"#5",-"#6",-"#7",-"#8",-"#9",-"#10"]
    local tvars: Array Symbol := [-"t#1",-"t#2",-"t#3",-"t#4",-"t#5",-"t#6",-"t#7",-"t#8",-"t#9",-"t#10"]

    local lookup(axSym: %, id: LibAttribute): SExpression ==
        import from AxiomLibrary
        lookup(rep(axSym).lib, rep(axSym).sym, id)

    local env(axSym: %): Env ==
        import from AxiomLibrary
        env rep(axSym).lib

    local typeSystem(axSym: %): TypeSystem ==
        import from AxiomLibrary
        typeSystem rep(axSym).lib

    local annotate(e: Env, ab: AbSyn): AnnotatedAbSyn ==
        import from AbSynAnnotator
        annotateSym(sym: Symbol): AnnotatedId ==
            if sym = -"$" then sym := -"%"
            (flg, pos, val) := linearSearch(sym, tvars)
            flg => newAnnotatedId(e, vars.pos)
            newAnnotatedId(e, sym)
        annotate(annotateSym, ab)

    definedSymbol(axSym: %): Symbol == rep(axSym).sym

    newAxiomSymbol(sym: Symbol, lib: AxiomLibrary): % == per [sym, lib]

    kind(axSym: %): SymbolKind ==
        sx := lookup(axSym, libAttrConstructorKind)
        stdout << "Kind " << axSym << " " << sx << newline
        valueOf(sym sx)$SymbolKind

    constructorModemap(axSym: %): ConstructorModemap ==
        sx := lookup(axSym, libAttrConstructorModemap)
        newConstructorModemap sx

    domainForm(sym: %): TForm ==
        --stdout << "(DomainForm " << sym << newline
        df := domainForm1 sym
        --stdout << " DomainForm " << sym << " = " << df << ")" << newline
        df

    local domainForm1(sym: %): TForm ==
        import from MachineInteger, Array Symbol
        modemap: ConstructorModemap := constructorModemap sym
        form := symForm modemap
        if nil? rest form then
            boundCategory(sym)
        else
            newMap([placeholderTForm vars.i for i in 0.. for sx in rest form], [boundCategory sym])

    categoryForm(sym: %): TForm ==
        stdout << "(CategoryForm " << sym << newline
        df := categoryForm1 sym
        stdout << " CategoryForm " << sym << " = " << df << ")" << newline
        df

    constructorForm(axSym: %): AnnotatedAbSyn ==
        sx := lookup(axSym, libAttrConstructorForm)
        annotate(env axSym, parse sx)

    local categoryForm1(sym: %): TForm ==
        import from List AbSyn
        import from SExpression
        form := symForm constructorModemap sym
        if nil? rest form then
            thisCat: TForm := newSyntax(typeSystem sym, canonicalise annotate(env sym, parseSExpression form))
            newThird(cons(thisCat, append!(parents sym, operations sym)))
        else
            tbl: HashTable(Symbol, TForm) := [(vars.i, Type$TForm) for i in 0.. for sx in rest form]
            microEnv: Env := newEnv((a: Symbol): Partial TForm +-> find(a, tbl), env sym)
            self: AbSyn := newApply(parseSExpression first form, [newId vars.i for i in 0.. for sx in rest form])
            thisCat: TForm := newSyntax(typeSystem sym, canonicalise annotate(microEnv, self))
            thisThird := newThird(cons(thisCat, append!(parents sym, operations sym)))
            newMap([placeholderTForm vars.i for i in 0.. for sx in rest form], [thisThird])

    -- NB: Need to add in the type of sx
    local placeholderTForm(sym: Symbol): TForm == newDeclare(sym, Type$TForm)

    local category(sym: %): TForm ==
        form: SExpression := symForm constructorModemap sym
        thisCat: TForm := newSyntax(typeSystem sym, annotate(env sym, parseSExpression form))
        newThird(cons(thisCat, append!(parents sym, operations sym)))

    local boundCategory(sym: %): TForm ==
        bind(newCategory(append!(parents sym, operations sym)),
             annotate(env sym, parseSExpression symForm constructorModemap sym))

    local parents(axSym: %): List TForm == directParents axSym

    local operations(axSym: %): List TForm == directOperations axSym

    local directParents(axSym: %): List TForm ==
        import from TForm
        local parent(sx: SExpression, cond: List SExpression): List TForm ==
            [newSyntax(typeSystem axSym, canonicalise(annotate(env axSym, parseSExpression sx)))]
        signature(sx: SExpression, cond: List SExpression): List TForm == []
        directCategorySearch(TForm)(axSym, signature, parent)

    local directOperations(axSym: %): List TForm ==
        import from TForm
        sxToType(argsx: SExpression): TForm == newSyntax(typeSystem axSym, canonicalise annotate(env axSym, parseSExpression argsx))
        parent(sx: SExpression, cond: List SExpression): List TForm == []
        signature(sx: SExpression, cond: List SExpression): List TForm ==
            --stdout << "Signature: " << sx << newline
            (name, sx) := (first sx, rest sx)
            (sig, sx) := (first sx, rest sx)
            --stdout << "Name: " << name << " sig: " << sig << " rest: " << sx << newline

            const? := not nil? sx
            sxCond: SExpression := cons(sexpr(-"AND"), [c for c in cond])
            const? =>
                if cons? name then name := first name
                [newSignature(sym name, sxToType first sig, sxCond)]
            [newSignature(sym name, newMap(newMulti([sxToType arg for arg in rest sig]), sxToType(first sig)), sxCond)]
        ops := directCategorySearch(TForm)(axSym, signature, parent)
        return ops

    SxCondPair ==> (SExpression, List SExpression)

    local directCategorySearch(T: with)(axSym: %, sig: SxCondPair -> List T, parent: SxCondPair -> List T): List T ==
        import from List SExpression, Fold2 List T, Integer

        makeParentSeq(sx: SExpression, conditions: List SExpression): List T ==
            (append!,[])/(makeParent(expr, conditions) for expr in sx)

        makeParent(sx: SExpression, conditions: List SExpression): List T ==
            import from Symbol
            sx = sexpr(-"noBranch") => []
            first sx = sexpr(-"CATEGORY") =>
                -- [CATEGORY constructorKind,:parent]
                (append!, [])/(makeParent(parentsx, conditions) for parentsx in rest rest sx)
            first sx = sexpr(-"Join") => makeParentSeq(rest sx, conditions)
            first sx = sexpr(-"PROGN") => makeParentSeq(rest sx, conditions)
            first sx = sexpr(-"IF") =>
                (p, q, r) := (nth(sx, 1), nth(sx, 2), nth(sx, 3))
                lhs: List T := makeParent(q, cons(p, conditions))
                rhs: List T := makeParent(r, cons(cons(sexpr(-"NOT"), p), conditions))
                append!(lhs, rhs)
            first sx = sexpr(-"SIGNATURE") => sig(rest sx, conditions)
            first sx = sexpr(-"ATTRIBUTE") => makeParent(first rest sx, conditions)
            parent((sx, conditions))
        makeParent(lookup(axSym, libAttrConstructorCategory), [])

    local makeSignature(typeSystem: TypeSystem, e: Env, name: Symbol, sx: SExpression): TForm ==
        safeFirst(sx: SExpression): SExpression == if nil? sx then nil else first sx
        safeRest(sx: SExpression): SExpression == if nil? sx then nil else rest sx

        (sigSx, sx) := (first sx, rest sx)
        (slot, sx) := (first sx, rest sx)
        (cond, sx) := (safeFirst sx, safeRest sx)
        (const, sx) := (safeFirst sx, safeRest sx)

        sxToType(argsx: SExpression): TForm == newSyntax(typeSystem, canonicalise annotate(e, parseSExpression argsx))
        args(argsx: SExpression): TForm ==
            newMulti([sxToType part for part in argsx])

        tf := if not nil? const then sxToType(first sigSx) else newMap(args(rest sigSx), sxToType(first sigSx))

        newSignature(name, tf, cond)

    local signatures(sx: SExpression): List SExpression ==
        import from Fold2 List SExpression
        import from Integer
        not cons? sx => []
        first sx = sexpr(-"SIGNATURE") => [sx]
        first sx = sexpr(-"Join") or first sx = sexpr(-"PROGN") => (append!, [])/(signatures x for x in rest sx)
        first sx = sexpr(-"TYPE") => []
        first sx = sexpr(-"ATTRIBUTE") => []
        first sx = sexpr(-"IF") =>
            (p, q, r) := (nth(sx, 1), nth(sx, 2), nth(sx, 3))
            append!(signatures q, signatures r)
        []

    local parents(sx: SExpression): SExpression ==
        import from Fold2 SExpression
        import from Integer
        not cons? sx => []
        first sx = sexpr(-"SIGNATURE") => nil
        first sx = sexpr(-"Join") or first sx = sexpr(-"PROGN") => [generate for childsx in sx repeat for gensx in parents(childsx) repeat yield gensx]
        first sx = sexpr(-"TYPE") => nil
        first sx = sexpr(-"ATTRIBUTE") =>
            cons? first rest sx => parents first rest sx
            nil
        first sx = sexpr(-"IF") =>
            (p, q, r) := (nth(sx, 1), nth(sx, 2), nth(sx, 3))
            cons? q or cons? r =>
                [[sexpr(-"IF"), p, parents q, parents r]]
            nil
        []

    (out: TextWriter) << (axSym: %): TextWriter ==
        import from Symbol
        out << rep(axSym).sym

AxiomLibrary: with
    newLibrary: (TypeSystem, Env, SymbolDatabase) -> %
    env: % -> Env
    tform: (%, Symbol) -> Partial TForm
    typeSystem: % -> TypeSystem
    ids: % -> List Symbol
    symbol: (%, Symbol) -> AxiomSymbol
    lookup: (%, Symbol, LibAttribute) -> SExpression
== add
    Rep == Record(path: String,
                  ts: TypeSystem,
                  env: Env,
                  files: HashTable(Symbol, AxiomSymbol),
                  db: SymbolDatabase)
    import from Rep
    import from AxiomSymbol, IndexedFile, HashTable(Symbol, AxiomSymbol)

    lookup(lib: %, sym: Symbol, id: LibAttribute): SExpression ==
        import from SymbolDatabase
        get(rep(lib).db, sym)(id)

    symbol(lib: %, sym: Symbol): AxiomSymbol == rep(lib).files.sym

    env(lib: %): Env ==
        lookup(sym: Symbol): Partial TForm ==
            import from SExpression, TForm
            ptf := tform(lib, sym)
            if not failed? ptf then stdout << "Lookup: " << sym << " " << sexpression retract ptf << newline
            ptf
        newEnv(lookup, rep(lib).env)

    ids(lib: %): List Symbol == [key for (key, value) in rep(lib).files]

    typeSystem(lib: %): TypeSystem == rep(lib).ts

    newLibrary(ts: TypeSystem, e: Env, db: SymbolDatabase): % ==
        import from List Symbol
        rec := per [name db, ts, e, table(), db]
        for sym in (makeSymbol(rec, sym) for sym in symbols db) repeat
            import from Symbol
            rep(rec).files.(definedSymbol sym) := sym
        rec


    local makeSymbol(lib: %, sym: Symbol): AxiomSymbol == newAxiomSymbol(sym, lib)

    local axiomSymbol(lib: %, sym: Symbol): Partial AxiomSymbol ==
        import from Partial AxiomSymbol
        r := find(sym, rep(lib).files)
        if failed? r then
            stdout << "Failed to find " << sym << " in " << rep(lib).path << newline
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
        theKind = package =>
            [domainForm(retract axSym)]
        theKind = category =>
            [categoryForm(retract axSym)]
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
