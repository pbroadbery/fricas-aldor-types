#include "aldor"
#include "aldorio"
#pile
#library SpadTypeLib "libSpadType.al"
import from SpadTypeLib
inline from SpadTypeLib

+++ Generic fun type facts
TypeInfo: with
    PrimitiveType
    OutputType
    typeInfo: (Symbol, TForm -> Boolean) -> %
    id: % -> Symbol
    category?: (%, TForm) -> Boolean
== add
    Rep == Record(id: Symbol, catfn: TForm -> Boolean)
    import from Rep

    typeInfo(id: Symbol, catfn: TForm -> Boolean): % == per [id, catfn]

    id(inf: %): Symbol == rep(inf).id
    category?(inf: %, tf: TForm): Boolean == (rep(inf).catfn)(tf)

    (a: %) = (b: %): Boolean == id a = id b
    (out: TextWriter) << (inf: %): TextWriter == out << id inf

-- missing things:
--- 1: Condition evaluation
--- 2: Type inference of apply arguments
--- 3: Record/Union types
--- 5: Aldor type mapping

--+++ A type form.  Generally types.
TForm: OutputType with
    HashType
    PointerType
    Type: % -- type of all types
    Category: % -- type of all categories
    newCategory: List % -> %
    newThird: List % -> %
    newDeclare: (Symbol, %) -> %
    newIf: (SExpression, %) -> %
    newMap: (%, %) -> %
    newMap: (List %, List %) -> %
    newMulti: List % -> %
    newSignature: (Symbol, %, SExpression) -> %
    newSyntax: (TypeSystem, AnnotatedAbSyn) -> %
    id: % -> Symbol

    bind: (%, AnnotatedAbSyn) -> %
    boundSyntax: % -> AnnotatedAbSyn

    catParents: % -> List %
    domImports: % -> List SymbolMeaning

    subst: (%, AbSub) -> %
    inner: % -> AnyTForm

    typeInfo: % -> TypeInfo
    category?: % -> Boolean
== add
    UTF == Union(m: TfMap, gen: TfGeneral, type: TfType, catType: TfCatType,
                   declare: TfDeclare, cat: TfCategory, thd: TfThird, tfIf: TfIf, sig: TfSignature, multi: TfMulti)
    Rep == Record(ab: AnnotatedAbSyn, inner: AnyTForm)
    import from Rep, UTF, AnyTForm, AnnotatedAbSyn, Symbol
    import from SymbolMeaning

    (tf1: %) = (tf2: %): Boolean ==
        rep(tf1).ab = rep(tf2).ab and rep(tf1).inner = rep(tf2).inner

    is?(tf: %, sym: Symbol): Boolean == id tf = sym

    hash(tf: %): MachineInteger == 0

    Type: % == per [newNone(), anyForm [type()$TfType]] -- per [newId(-"Type"), anyForm [type()$TfType]]
    Category: % == per [newNone(), anyForm [catType()$TfCatType]] -- per [newId(-"Category"), anyForm [catType()$TfCatType]]
    newCategory(parents: List %): % ==
        per [newNone(), anyForm [newTfCategory(parents)]]
    newThird(parents: List %): % ==
           per [newNone(), anyForm [newTfThird(newCategory(parents))]]
    newDeclare(sym: Symbol, type: %): % == per [newNone(), anyForm [newTfDeclare(sym, type)]]
    newIf(cond: SExpression, pos: %): % == per [newNone(), anyForm [newTfIf(cond, pos)]]
    newMap(arg: %, ret: %): % == per [newNone(), anyForm [newTfMap(arg, ret)]]
    newMap(args: List %, rets: List %): % == per [newNone(), anyForm [newTfMap(newMulti args, newMulti rets)]]
    newMulti(l: List %): % == per [newNone(), anyForm [newTfMulti(l)]]
    newSignature(sym: Symbol, type: %, cond: SExpression): % ==
        syme := newSymbolMeaning(sym, type)
        per [newNone(), anyForm [newTfSignature(syme, cond)]]

    newSyntax(ts: TypeSystem, ab: AnnotatedAbSyn): % == per [newNone(), anyForm [newTfGeneral(ts, ab)]]

    id(tf: %): Symbol == id inner tf
    typeInfo(tf: %): TypeInfo == typeInfo inner tf
    inner(tf: %): AnyTForm == rep(tf).inner

    boundSyntax(tf: %): AnnotatedAbSyn == rep(tf).ab

    catParents(tf: %): List % == catParents inner tf
    domImports(tf: %): List SymbolMeaning == domImports inner tf

    -- from typeInfo
    category?(tf: %): Boolean ==
        import from TypeInfo
        category?(typeInfo tf, tf)

    (out: TextWriter) << (tf: %): TextWriter ==
        none? boundSyntax tf => out << rep(tf).inner
        out << "{ " << boundSyntax tf << " == " << rep(tf).inner << "}"

    bind(tf: %, bound: AnnotatedAbSyn): % == per [bound, rep(tf).inner]

    subst(tf: %, sigma: AbSub): % ==
        import from SubstitutionPackage, AnyTForm
        any := subst(anyForm tf, sigma)
        per [subst(sigma, rep(tf).ab), any]

    anyForm(tf: TForm): AnyTForm == rep(tf).inner

    anyForm(utf: UTF): AnyTForm == select utf in
        m => anyTForm(TfMap, utf.m)
        gen => anyTForm(TfGeneral, utf.gen)
        type => anyTForm(TfType, utf.type)
        catType => anyTForm(TfCatType, utf.catType)
        declare => anyTForm(TfDeclare, utf.declare)
        cat => anyTForm(TfCategory, utf.cat)
        tfIf => anyTForm(TfIf, utf.tfIf)
        sig => anyTForm(TfSignature, utf.sig)
        multi => anyTForm(TfMulti, utf.multi)
        thd => anyTForm(TfThird, utf.thd)
        never

AnyTForm: OutputType with
    PrimitiveType
    anyTForm: (T: TFormSubType, T) -> %
    subst: (%, AbSub) -> %
    id: % -> Symbol
    typeInfo: % -> TypeInfo
    toSubType: (X: TFormSubType, %) -> X
    catParents: % -> List TForm

    domImports: % -> List SymbolMeaning
== add
    Rep == Record(c: Cross(T: TFormSubType, T))

    import from Rep, Symbol
    anyTForm(T: TFormSubType, t: T): % == per [pair(T, t)]
    toSubType(X: TFormSubType, any: %): X ==
        toSubType0(T: TFormSubType, t: T): X == t pretend X
        toSubType0 unwrap any

    local unwrap(atf: %): (T: TFormSubType, t: T) ==
        pp: Cross(T: TFormSubType, t: T) == rep(atf).c
        pp

    local pair(T: TFormSubType, t: T): (T1: TFormSubType, t: T1)  == (T, t)

    id(atf: %): Symbol ==
        id0(T: TFormSubType, t: T): Symbol == id$T
        id0 unwrap atf

    typeInfo(atf: %): TypeInfo ==
        info0(T: TFormSubType, t: T): TypeInfo == typeInfo$T
        info0 unwrap atf


    subst(anyTf: %, sigma: AbSub): % ==
        subst1(T: TFormSubType, tf: T): % == anyTForm(T, subst(tf, sigma))
        subst1 unwrap anyTf

    catParents(anyTf: %): List TForm ==
        catParents1(T: TFormSubType, tf: T): List TForm == catParents tf
        catParents1 unwrap anyTf

    domImports(anyTf: %): List SymbolMeaning ==
        domImports1(T: TFormSubType, tf: T): List SymbolMeaning == domImports tf
        domImports1 unwrap anyTf

    (anyTf1: %) = (anyTf2: %): Boolean ==
        eq(T1: TFormSubType, tf1: T1)(T2: TFormSubType, tf2: T2): Boolean ==
            id$T1 = id$T2 and tf1 = (tf2 pretend T1)
        eq (unwrap anyTf1) (unwrap anyTf2)

    (out: TextWriter) << (atf: %): TextWriter ==
        (T: TFormSubType, t: T) == unwrap atf
        import from T
        out << t

TFormSubType: Category == OutputType with
    PrimitiveType
    subst: (%, AbSub) -> %
    id: Symbol
    typeInfo: TypeInfo
    coerce: TForm -> %
    catParents: % -> List TForm
    domImports: % -> List SymbolMeaning
    default
        coerce(tf: TForm): % ==
            import from AnyTForm
            id tf ~= id => error("found a " + (toString id tf) + " expected " + (toString id)  + " type: " + (toString tf))
            toSubType(%, inner tf)

        catParents(stf: %): List TForm == []
        domImports(stf: %): List SymbolMeaning == error("domImports not implemented " + toString id)

        (tf1: %) = (tf2: %): Boolean ==
            import from Symbol
            error("no eq for " + (toString id))

TfType: TFormSubType with
    type: () -> %
    theType?: TForm -> Boolean
== add
    Rep == MachineInteger -- anything(!)
    import from Rep
    type(): % == per 1
    (out: TextWriter) << (t: %): TextWriter == out << "{Type}"
    subst(tf: %, sigma: AbSub): % == tf
    id: Symbol == -"type"
    theType?(tf: TForm): Boolean == id$% = id tf

    typeInfo: TypeInfo == typeInfo(id, (a: TForm): Boolean +-> false)

TfCatType: TFormSubType with
    catType: () -> %
    catType?: TForm -> Boolean
== add
    Rep == MachineInteger -- anything(!)
    import from Rep
    catType(): % == per 1
    (out: TextWriter) << (t: %): TextWriter == out << "{CatType}"
    subst(tf: %, sigma: AbSub): % == tf
    id: Symbol == -"categpry"
    catType?(tf: TForm): Boolean == id$% = id tf
    typeInfo: TypeInfo == typeInfo(id, (a: TForm): Boolean +-> false)

TfGeneral: TFormSubType with
    newTfGeneral: (TypeSystem, AnnotatedAbSyn) -> %
    syntax: % -> AnnotatedAbSyn
    type: % -> TForm
    general?: TForm -> Boolean
== add
    Rep == Record(ts: TypeSystem, ab: AnnotatedAbSyn)
    import from Rep, SubstitutionPackage

    general?(tf: TForm): Boolean == id$% = id tf

    id: Symbol == -"general"

    newTfGeneral(ts: TypeSystem, ab: AnnotatedAbSyn): % ==
        import from AnnotatedId, Partial TForm
        id? ab => per [ts, ab]
        per [ts, ab]

    syntax(tf: %): AnnotatedAbSyn == rep(tf).ab

    type(tf: %): TForm == infer(rep(tf).ts, rep(tf).ab)

    (tf1: %) = (tf2: %): Boolean == rep(tf1).ab = rep(tf2).ab

    (out: TextWriter) << (t: %): TextWriter == out << "{" << syntax t << "}"
    subst(tf: %, sigma: AbSub): % == newTfGeneral(rep(tf).ts, subst(sigma, syntax tf))

    local typeIsThirdOrCategory?(tf: TForm): Boolean ==
        import from TfCatType, TfThird
        myType := type(tf::TfGeneral)
        third? myType or catType? myType

    typeInfo: TypeInfo == typeInfo(id, typeIsThirdOrCategory?)

    catParents(tf: %): List TForm ==
        stdout << "catparents: gen " << tf << newline
        import from TfThird
        myType: TForm := type tf
        not third? myType => []
        thdParents(myType::TfThird)

    domImports(tf: %): List SymbolMeaning ==
        import from SymbolMeaning, Export, TForm, TypePackage
        catTf: TForm := type tf
        sigma: AbSub := newSubst(-"%", syntax tf)
        exports: List Export := catExports catTf
        [newSymbolMeaning(name exp, subst(type exp, sigma)) for exp in exports]

TfIf: TFormSubType with
    if?: TForm -> Boolean
    condition: % -> SExpression -- temp
    value: % -> TForm
    newTfIf: (SExpression, TForm) -> %
== add
    Rep == Record(cond: SExpression, value: TForm)
    import from Rep

    id: Symbol == -"if"
    if?(tf: TForm): Boolean == id$% = id tf

    typeInfo: TypeInfo == typeInfo(id, (tf: TForm): Boolean +-> false)

    condition(tfIf: %): SExpression == rep(tfIf).cond
    value(tfIf: %): TForm == rep(tfIf).value
    import from Rep

    newTfIf(cond: SExpression, val: TForm): % == per [cond, val]
    (out: TextWriter) << (tf: %): TextWriter == out << "{If " << condition tf  << "}"
    subst(tf: %, sigma: AbSub): % == newTfIf(condition tf, subst(value tf, sigma))

TfThird: TFormSubType with
    cat: % -> TForm -- probably a category
    newTfThird: TForm -> %
    third?: TForm -> Boolean
    thdExports: % -> List Export
    thdParents: % -> List TForm
== add
    Rep == TForm
    import from Rep
    id: Symbol == -"third"
    newTfThird(tf: TForm): % == per tf
    third?(tf: TForm): Boolean == id tf = id
    cat(tf: %): TForm == rep tf

    subst(tf: %, sigma: AbSub): % == newTfThird(subst(cat tf, sigma))
    (out: TextWriter) << (tf: %): TextWriter == out << "{thd " << rep tf << "}"

    thdExports(tf: %): List Export ==
        import from TypePackage
        catExports rep tf

    thdParents(tf: %): List TForm ==
        stdout << "thdparents: " << id << " " << tf << newline
        catParents rep tf

    typeInfo: TypeInfo == typeInfo(id, (tf: TForm): Boolean +-> false)

TfCategory: TFormSubType with
    parents: % -> List TForm
    newTfCategory: List TForm -> %
    categoryForm?: TForm -> Boolean
== add
    Rep == Record(parents: List TForm)
    import from Rep, List TForm

    id: Symbol == -"cat"
    categoryForm?(tf: TForm): Boolean == id$% = id tf
    newTfCategory(parents: List TForm): % == per [parents]
    parents(cat: %): List TForm == rep(cat).parents

    catParents(cat: %): List TForm == rep(cat).parents
    catExports(cat: %): List Export == []

    (out: TextWriter) << (t: %): TextWriter == out << "{Cat " << parents(t) << "}"

    subst(tf: %, sigma: AbSub): % ==
        import from TForm
        newTfCategory([subst(part, sigma) for part in parents tf])

    typeInfo: TypeInfo == typeInfo(id, (tf: TForm): Boolean +-> true)

    (a: %) = (b: %): Boolean == never

TfSignature: TFormSubType with
    signature?: TForm -> Boolean
    symbolMeaning: % -> SymbolMeaning
    signature: % -> Export
    newTfSignature: (SymbolMeaning, SExpression) -> %
== add
    Rep == Record(sym: SymbolMeaning, cond: SExpression)
    import from Rep

    id: Symbol == -"sig"
    signature?(tf: TForm): Boolean == id$% = id tf
    newTfSignature(sig: SymbolMeaning, cond: SExpression): % == per [sig, cond]
    symbolMeaning(sig: %): SymbolMeaning == rep(sig).sym
    (out: TextWriter) << (t: %): TextWriter == out << "{Sig" << "}"
    subst(tf: %, sigma: AbSub): % ==
        import from SymbolMeaning
        newTfSignature(subst(symbolMeaning tf, sigma), rep(tf).cond)

    signature(tf: %): Export == newExport(name symbolMeaning tf, type symbolMeaning tf, rep(tf).cond)

    typeInfo: TypeInfo == typeInfo(id, (tf: TForm): Boolean +-> false)

TfMap: TFormSubType with
    arg: % -> TForm
    ret: % -> TForm
    args: % -> List TForm
    rets: % -> List TForm
    newTfMap: (TForm, TForm) -> %
    map?: TForm -> Boolean
== add
    Rep == Record(arg: TForm, ret: TForm)
    import from Rep, List TForm, TForm, TfMulti

    id: Symbol == -"map"

    map?(tf: TForm): Boolean == id tf = id$%

    newTfMap(args: TForm, ret: TForm): % ==
        args := if multi? args then args else newMulti [args]
        ret := if multi? ret then ret else newMulti [ret]
        per [args, ret]

    arg(m: %): TForm == rep(m).arg
    ret(m: %): TForm == rep(m).ret

    args(m: %): List TForm == parts(rep(m).arg::TfMulti)
    rets(m: %): List TForm == parts(rep(m).ret::TfMulti)

    (tf1: %) = (tf2: %): Boolean == arg tf1 = arg tf2 and ret tf1 = ret tf2

    subst(tf: %, sigma: AbSub): % ==
        newTfMap(subst(arg tf, sigma), subst(ret tf, sigma))

    (out: TextWriter) << (t: %): TextWriter == out << "{" << args t << " -> " << ret t << "}"

    typeInfo: TypeInfo == typeInfo(id$%, (tf: TForm): Boolean +-> false)

TfDeclare: TFormSubType with
    newTfDeclare: (Symbol, TForm) -> %
    declare?: TForm -> Boolean
    sym: % -> Symbol
    annotatedId: % -> AnnotatedId
    type: % -> TForm
    modDeclare: TForm -> TForm
== add
    Rep == Record(sym: Symbol, tf: TForm)
    import from Rep, Symbol

    id: Symbol == -"declare"
    declare?(tf: TForm): Boolean == id$% = id tf
    newTfDeclare(sym: Symbol, tf: TForm): % == per [sym, tf]
    sym(decl: %): Symbol == rep(decl).sym
    type(decl: %): TForm == rep(decl).tf
    annotatedId(decl: %): AnnotatedId == never

    modDeclare(tf: TForm): TForm == if declare? tf then type(tf::TfDeclare) else tf

    (out: TextWriter) << (t: %): TextWriter == out << "{" << sym t << ": " << type t << "}"
    subst(tf: %, sigma: AbSub): % == newTfDeclare(sym tf, subst(type tf, sigma))

    typeInfo: TypeInfo == typeInfo(id, (tf: TForm): Boolean +-> (inner := type(tf::TfDeclare); category?(typeInfo inner, inner)))

TfMulti: TFormSubType with
    newTfMulti: List  TForm -> %
    multi?: TForm -> Boolean
    parts: % -> List TForm
== add
    Rep == List TForm
    import from Rep, TForm

    id: Symbol == -"multi"
    multi?(tf: TForm): Boolean == id$% = id tf
    newTfMulti(l: List TForm): % == per l

    parts(t: %): List TForm == rep t

    (tf1: %) = (tf2: %): Boolean == rep tf1 = rep tf2

    (out: TextWriter) << (t: %): TextWriter == out << "{" << rep t << "}"
    subst(tf: %, sigma: AbSub): % == newTfMulti [subst(part, sigma) for part in rep tf]

    typeInfo: TypeInfo == typeInfo(id, (tf: TForm): Boolean +-> false)

#if 0
TfRecord: TFormSubType with
    newTfRecord: (List Symbol) -> %
== add

#endif

SymbolMeaning: OutputType with
    newSymbolMeaning: (Symbol, TForm) -> %
    name: % -> Symbol
    type: % -> TForm
    subst: (%, AbSub) -> %
== add
    Rep == Record(name: Symbol, type: TForm)
    import from Rep

    newSymbolMeaning(sym: Symbol, tf: TForm): % == per [sym, tf]

    name(syme: %): Symbol == rep(syme).name
    type(syme: %): TForm == rep(syme).type

    subst(syme: %, sigma: AbSub): % == newSymbolMeaning(name syme, subst(type syme, sigma))

    (out: TextWriter) << (syme: %): TextWriter == out << "{S: " << name syme << "}"

Export: OutputType with
    newExport: (Symbol, TForm, SExpression) -> %
    name: % -> Symbol
    type: % -> TForm
    subst: (%, AbSub) -> %
== add
    Rep == Record(name: Symbol, tf: TForm, condition: SExpression)
    import from Rep
    newExport(s: Symbol, tf: TForm, cond: SExpression): % == per [s, tf, cond]
    name(e: %): Symbol == rep(e).name
    type(e: %): TForm == rep(e).tf

    subst(e: %, sigma: AbSub): % == newExport(name e, subst(type e, sigma), rep(e).condition)

    (out: TextWriter) << (exp: %): TextWriter == out << "{S: " << name exp << " " << type exp << "}"

AbSub: OutputType with
    emptySubst: () -> %
    newSubst: (Symbol, AnnotatedAbSyn) -> %
    bracket: Generator Cross(Symbol, AnnotatedAbSyn) -> %
    lookup: (%, Symbol) -> Partial AnnotatedAbSyn
== add
    Rep == HashTable(Symbol, AnnotatedAbSyn)
    import from Rep

    emptySubst(): % == per table()
    newSubst(sym: Symbol, ab: AnnotatedAbSyn): % == per [(sym, ab)@Cross(Symbol, AnnotatedAbSyn)]
    [g: Generator Cross(Symbol, AnnotatedAbSyn)]: % == per [g]

    lookup(sigma: %, sym: Symbol): Partial AnnotatedAbSyn == find(sym, rep(sigma))

    (out: TextWriter) << (sigma: %): TextWriter == out << rep sigma

SubstitutionPackage: with
    subst: (AbSub, AnnotatedAbSyn) -> AnnotatedAbSyn
== add
    import from List AnnotatedAbSyn, AnnotatedId

    subst(sigma: AbSub, ab: AnnotatedAbSyn): AnnotatedAbSyn ==
        id? ab =>
            abMaybe: Partial AnnotatedAbSyn := lookup(sigma, id idSymbol ab)
            failed? abMaybe => ab
            retract abMaybe
        apply? ab => newApply(subst(sigma, applyOperator ab), [subst(sigma, arg) for arg in applyArguments ab])
        none? ab => ab
        literal? ab => ab
        declare? ab => newDeclare(declareId ab, subst(sigma, declareType ab))
        error("unknown absyn: " + toString ab)

Env: with
    lookup: (%, Symbol) -> Partial TForm
    newEnv: (Symbol -> Partial TForm, %) -> %
    emptyEnv: (AnnotatedAbSyn -> TForm) -> %
    infer: (%, AnnotatedAbSyn) -> TForm
== add
    Level == Record(lookup: Symbol -> Partial TForm, infer: AnnotatedAbSyn -> TForm)
    Rep == List(Level)
    import from Rep, Level

    emptyEnv(f: AnnotatedAbSyn -> TForm): % == per [[(s: Symbol): Partial TForm +-> failed, f]]
    newEnv(f: Symbol -> Partial TForm, e: %): % ==
        per cons([f, first(rep(e)).infer], rep e)

    lookup(env: %, s: Symbol): Partial TForm ==
        for lvl in rep(env) repeat
            ptf := (lvl.lookup)(s)
            not failed? ptf => return ptf
        failed

    infer(e: %, ab: AnnotatedAbSyn): TForm ==
        stdout << "(env infer: " << ab << newline
        res := first(rep(e)).infer(ab)
        stdout << " env infer: " << ab << " res == " << res << ")" <<newline
        res

AnnotatedId: with
    PrimitiveType
    SExpressionOutputType
    id: % -> Symbol
    env: % -> Env
    newAnnotatedId: (Env, Symbol) -> %
    type: % -> TForm
== add
    Rep == Record(e: Env, id: Symbol)
    import from Rep

    newAnnotatedId(e: Env, sym: Symbol): % == per [e, sym]
    id(aid: %): Symbol == rep(aid).id
    env(aid: %): Env == rep(aid).e

    (a: %) = (b: %): Boolean ==
        import from Symbol
        id a = id b -- env equality not implemented, so not 100% safe

    sexpression(aid: %): SExpression == sexpr id aid

    type(aid: %): TForm ==
        ptf: Partial TForm := lookup(env aid, id aid)
        failed? ptf => error("Unknown: " + name id(aid))
        retract ptf

AnnotatedAbSyn: AbSynCategory AnnotatedId with
    OutputType
    PrimitiveType
== AbSynAny AnnotatedId add

AbSynAnnotator: with
    annotate: (Symbol -> AnnotatedId, AbSyn) -> AnnotatedAbSyn
== add
    annotate(fn: Symbol -> AnnotatedId, ab: AbSyn): AnnotatedAbSyn ==
        import from List AnnotatedAbSyn, List AbSyn
        none? ab => newNone()
        apply? ab => newApply(annotate(fn, applyOperator ab), [annotate(fn, arg) for arg in applyArguments ab])
        id? ab => newId(fn idSymbol ab)
        literal? ab => newLiteral literal ab
        declare? ab => newDeclare(fn declareId ab, annotate(fn, declareType ab))
        error("unknown absyn to annotate" + (toString ab))

SatResultCategory: Category == Join(PrimitiveType, OutputType) with
    success?: % -> Boolean
    sigma: % -> AbSub

SatisfierCategory: Category == with
    satisfies: (%, TForm, TForm) -> SatResult

FnSatisfier: SatisfierCategory with
    coerce: ((TForm, TForm) -> SatResult) -> %
== add
    Rep ==> ((TForm, TForm) -> SatResult)

    satisfies(sat: %, S: TForm, T: TForm): SatResult == (rep sat)(S, T)
    coerce(f: Rep): % == per f

TypeSystem: with
    create: (AnnotatedAbSyn -> TForm) -> %
    infer: (%, AnnotatedAbSyn) -> TForm
== add
    Rep == Record(f: AnnotatedAbSyn -> TForm)
    import from Rep
    create(f: AnnotatedAbSyn -> TForm): % == per [f]
    infer(ts: %, ab: AnnotatedAbSyn): TForm == rep(ts).f(ab)

SatResult: SatResultCategory with
    success: AbSub -> %
    success: () -> %
    failed: () -> %

    failed?: % -> Boolean
    success?: % -> Boolean
== add
    Rep == Partial AbSub
    import from Rep, AbSub

    success?(r: %): Boolean == not failed? r
    failed?(r: %): Boolean == failed? rep r

    success(sigma: AbSub): % == per [sigma]
    success(): % == success(emptySubst())
    failed(): % == per failed
    (a: %) = (b: %): Boolean == a = b

    sigma(r: %): AbSub == if failed? rep r then emptySubst() else retract rep r
    (out: TextWriter) << (sigma: %): TextWriter == out << rep sigma

TypePackage: with
    infer: (FnSatisfier, AnnotatedAbSyn) -> TForm
    catExports: TForm -> List Export
    allParents: TForm -> List TForm
    imports: TForm -> List SymbolMeaning
== add

    infer(sat: FnSatisfier, ab: AnnotatedAbSyn): TForm ==
        stdout << "(TypePackage:::Infer: " << ab << newline
        tf := infer1(sat, ab)
        stdout << " TypePackage::Infer: " << tf << ")" << newline
        tf

    local infer1(sat: FnSatisfier, ab: AnnotatedAbSyn): TForm ==
        id? ab => inferId ab
        apply? ab => inferApply(sat, ab)
        none? ab => Type$TForm
        declare? ab => infer(sat, declareType ab)
        never

    local inferId(ab: AnnotatedAbSyn): TForm ==
        import from AnnotatedId
        import from Partial TForm, Env
        ptf: Partial TForm := lookup(env idSymbol ab, id idSymbol ab)
        failed? ptf =>
            stdout << "no meaning for " << idSymbol ab << newline
            Type$TForm -- "Failed"?
        retract ptf

    local inferApply(sat: FnSatisfier, ab: AnnotatedAbSyn): TForm ==
        import from List AnnotatedAbSyn, List TForm, TfDeclare, TfMap, TfGeneral, TfMulti, TfThird
        opType := infer(sat, applyOperator ab)
        stdout << "inferApply: " << ab << " " << opType << newline
        argTypes := [infer(sat, arg) for arg in applyArguments(ab)]
        -- Do I need a satMap() with options?
        empty? argTypes and (category? opType or third? opType) => opType
        r: SatResult := satisfies(sat, newMulti argTypes, arg(opType::TfMap))
        stdout << "SAT: " << r << newline

        stdout << "Infer apply: " << ab << " " << opType << newline
        for argTf in args(opType::TfMap) repeat
            stdout << argTf << " " << declare? argTf << newline

        sigma: AbSub := [(sym(argTf::TfDeclare), arg) for arg in applyArguments ab for argTf in args(opType::TfMap) | declare? argTf]
        stdout << "Infer sigma: " << sigma << newline
        retType: TForm := first rets(opType::TfMap)
        subst(retType, sigma)

    imports(tf: TForm): List SymbolMeaning ==
        import from Symbol, Export
        import from List Export
        import from SymbolMeaning
        self: AnnotatedAbSyn := boundSyntax tf
        sigma: AbSub := newSubst(-"%", self)
        [newSymbolMeaning(name exp, subst(type exp, sigma)) for exp in catExports tf]

    catExports(tf: TForm): List Export ==
        import from AsPointer TForm
        expand(tf: TForm, seen: HashSet AsPointer TForm): (List Export, List TForm) ==
            import from TfSignature
            myExports: List Export := if signature? tf then [signature(tf::TfSignature)] else []
            (myExports, [child for child in catParents tf| not contains?(seen, toPointer child)])
        toDo: List TForm := [tf]
        seen: HashSet AsPointer TForm := [toPointer tf]
        exports: List Export := []
        while not empty? toDo repeat
            (exps, more) := expand(first toDo, seen)
            stdout << "Curr: " << first toDo << " more: " << more << newline
            exports := append!(exps, exports)
            insert!(seen, toPointer first toDo)
            toDo := append!(more, rest toDo)
        exports

    allParents1(tf: TForm): List TForm ==
        import from AsPointer TForm
        expand(tf: TForm, seen: HashSet AsPointer TForm): List TForm ==
            import from TfSignature
            [child for child in catParents tf| not contains?(seen, toPointer child)]
        toDo: List TForm := [tf]
        seen: HashSet AsPointer TForm := [toPointer tf]
        while not empty? toDo repeat
            more := expand(first toDo, seen)
            stdout << "Curr: " << first toDo << " more: " << more << newline
            toDo := append!(more, rest toDo)
        [fromPointer ptf for ptf in seen]

    allParents(tf: TForm): List TForm ==
        expand(tf: TForm, seen: HashSet TForm): List TForm ==
            import from TfSignature
            [child for child in catParents tf| not contains?(seen, child)]
        toDo: List TForm := [tf]
        seen: HashSet TForm := []
        while not empty? toDo repeat
            insert!(seen, first toDo)
            more := expand(first toDo, seen)
            stdout << "Curr: " << first toDo << " more: " << more << newline
            toDo := append!(more, rest toDo)
        [xtf for xtf in seen]
