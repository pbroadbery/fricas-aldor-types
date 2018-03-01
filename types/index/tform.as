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
    sexpression: (%, TForm) -> SExpression
    typeInfo: (Symbol, category?: TForm -> Boolean, parents: TForm -> List Export, sxfn: TForm -> SExpression) -> %
    id: % -> Symbol
    category?: (%, TForm) -> Boolean
    directCatParents: (%, TForm) -> List Export
== add
    Rep == Record(id: Symbol,
                  catfn: TForm -> Boolean,
                  parentfn: TForm -> List Export,
                  sxfn: TForm -> SExpression)
    import from Rep

    typeInfo(id: Symbol, catfn: TForm -> Boolean, parentfn: TForm -> List Export, sxfn: TForm -> SExpression): % == per [id, catfn, parentfn, sxfn]

    id(inf: %): Symbol == rep(inf).id
    category?(inf: %, tf: TForm): Boolean == (rep(inf).catfn)(tf)
    directCatParents(inf: %, tf: TForm): List Export == (rep(inf).parentfn)(tf)
    sexpression(inf: %, tf: TForm): SExpression == (rep(inf).sxfn)(tf)
    (a: %) = (b: %): Boolean == id a = id b
    (out: TextWriter) << (inf: %): TextWriter == out << id inf

-- missing things:
--- 1: Condition evaluation
--- 2: Type inference of apply arguments
--- 3: Record/Union types
--- 5: Aldor type mapping

--+++ A type form.  Generally types.
TForm: OutputType with
    SExpressionOutputType
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

    subst: (%, AbSub) -> %
    inner: % -> AnyTForm

    typeInfo: % -> TypeInfo
    category?: % -> Boolean
    directCatParents: % -> List Export
== add
    UTF == Union(m: TfMap, gen: TfGeneral, type: TfType, catType: TfCatType,
                   declare: TfDeclare, cat: TfCategory, thd: TfThird, tfIf: TfIf, sig: TfSignature, multi: TfMulti)
    Rep == Record(ab: AnnotatedAbSyn, inner: AnyTForm)
    import from Rep, UTF, AnyTForm, AnnotatedAbSyn, Symbol
    import from SymbolMeaning

    (tf1: %) = (tf2: %): Boolean ==
        same?(tf1, tf2) => true
        r := rep(tf1).ab = rep(tf2).ab and rep(tf1).inner = rep(tf2).inner
        --stdout << "Equals: " << tf1 << " = " << tf2 << " --> " << r << newline
        r

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

    newSyntax(ts: TypeSystem, ab: AnnotatedAbSyn): % ==
        per [newNone(), anyForm [newTfGeneral(ts, ab)]]

    id(tf: %): Symbol == id inner tf
    typeInfo(tf: %): TypeInfo == typeInfo inner tf
    inner(tf: %): AnyTForm == rep(tf).inner

    boundSyntax(tf: %): AnnotatedAbSyn == rep(tf).ab

    -- from typeInfo
    category?(tf: %): Boolean ==
        import from TypeInfo
        category?(typeInfo tf, tf)

    -- from typeInfo
    directCatParents(tf: %): List Export ==
        import from TypeInfo
        directCatParents(typeInfo tf, tf)

    (out: TextWriter) << (tf: %): TextWriter ==
        none? boundSyntax tf => out << rep(tf).inner
        out << "{ " << boundSyntax tf << " == " << rep(tf).inner << "}"

    sexpression(tf: %): SExpression ==
        import from TypeInfo
        none? boundSyntax tf => sexpression(typeInfo tf, tf)
        cons(sexpr(-"bind"), [sexpression boundSyntax tf, sexpression(typeInfo tf, tf)])

    bind(tf: %, bound: AnnotatedAbSyn): % == per [bound, rep(tf).inner]

    subst(tf: %, sigma: AbSub): % ==
        import from SubstitutionPackage, AnyTForm
        any := subst(anyForm tf, sigma)
        --stdout << "subst " << sigma << " " << tf << " " << per [rep(tf).ab, any] << newline
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

    default
        coerce(tf: TForm): % ==
            import from AnyTForm
            id tf ~= id => error("found a " + (toString id tf) + " expected " + (toString id)  + " type: " + (toString tf))
            toSubType(%, inner tf)

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

    typeInfo: TypeInfo == typeInfo(id,
                                   (a: TForm): Boolean +-> false,
                                   (a: TForm): List Export +-> [],
                                   (a: TForm): SExpression +-> sexpr(-"Type"))

TfCatType: TFormSubType with
    catType: () -> %
    catType?: TForm -> Boolean
== add
    Rep == MachineInteger -- anything(!)
    import from Rep
    catType(): % == per 1
    (out: TextWriter) << (t: %): TextWriter == out << "{CatType}"
    subst(tf: %, sigma: AbSub): % == tf
    id: Symbol == -"category"
    catType?(tf: TForm): Boolean == id$% = id tf
    typeInfo: TypeInfo == typeInfo(id,
                                   (a: TForm): Boolean +-> false,
                                   (a: TForm): List Export +-> [],
                                   (a: TForm): SExpression +-> sexpr(-"Category"))

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
        import from Partial TForm, MachineInteger
        id? ab => per [ts, ab]
        if apply? ab and applyArgCount ab = 0 then
            stdout << ab << newline
            never
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

    typeInfo: TypeInfo == typeInfo(id, typeIsThirdOrCategory?,
                                  (tf: TForm): List Export +-> parentExports(tf::%),
                                  (tf: TForm): SExpression +-> [sexpr(-"General"), sexpression(syntax(tf::%))])

    parentExports(tf: %): List Export ==
        import from TfThird
        myType: TForm := type(tf)
        stdout << "tfGeneral parents " << id myType << " " << myType << newline
        third? myType => thdParents(myType::TfThird)
        []

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

    typeInfo: TypeInfo == typeInfo(id,
                                   (tf: TForm): Boolean +-> false,
                                   (a: TForm): List Export +-> [],
                                   (a: TForm): SExpression +-> [sexpr(-"If"), condition(a::%), sexpression value(a::%)])

    condition(tfIf: %): SExpression == rep(tfIf).cond
    value(tfIf: %): TForm == rep(tfIf).value

    newTfIf(cond: SExpression, val: TForm): % == per [cond, val]
    (out: TextWriter) << (tf: %): TextWriter == out << "{If " << condition tf  << "}"
    subst(tf: %, sigma: AbSub): % == newTfIf(condition tf, subst(value tf, sigma))

    (tf1: %) = (tf2: %): Boolean == rep(tf1).value = rep(tf2).value


TfThird: TFormSubType with
    cat: % -> TForm -- probably a category
    newTfThird: TForm -> %
    third?: TForm -> Boolean
    thdParents: % -> List Export
== add
    Rep == TForm
    import from Rep
    id: Symbol == -"third"
    newTfThird(tf: TForm): % == per tf
    third?(tf: TForm): Boolean == id tf = id
    cat(tf: %): TForm == rep tf

    subst(tf: %, sigma: AbSub): % == newTfThird(subst(cat tf, sigma))
    (out: TextWriter) << (tf: %): TextWriter == out << "{thd " << rep tf << "}"

    thdParents(tf: %): List Export == directCatParents rep tf

    typeInfo: TypeInfo == typeInfo(id,
                                   (tf: TForm): Boolean +-> false,
                                   (a: TForm): List Export +-> [],
                                   (a: TForm): SExpression +-> [sexpr(-"Third"), sexpression cat(a::%)])

TfCategory: TFormSubType with
    newTfCategory: List TForm -> %
    categoryForm?: TForm -> Boolean
    parentExports: % -> List Export
== add
    Rep == Record(parents: List Export)
    import from Rep, List TForm, Export
    local selfSelf: Symbol := -"%%"
    id: Symbol == -"cat"
    categoryForm?(tf: TForm): Boolean == id$% = id tf
    newTfCategory(theParents: List TForm): % == per [[newExport(parent) for parent in theParents]]
    parents(cat: %): List TForm == [type e for e in rep(cat).parents]

    (out: TextWriter) << (t: %): TextWriter == out << "{Cat " << parents(t) << "}"

    subst(tf: %, sigma: AbSub): % ==
        import from TForm
        per [[subst(parentExport, sigma) for parentExport in parentExports tf]]

    typeInfo: TypeInfo == typeInfo(id,
                                   (tf: TForm): Boolean +-> true,
                                   (tf: TForm): List Export +-> parentExports(tf::%),
                                   (tf: TForm): SExpression +-> cons(sexpr id, [sexpression part for part in parents(tf::%)]))

    parentExports(tf: %): List Export == rep(tf).parents

    (a: %) = (b: %): Boolean == never

TfSignature: TFormSubType with
    signature?: TForm -> Boolean
    symbolMeaning: % -> SymbolMeaning
    newTfSignature: (SymbolMeaning, SExpression) -> %
== add
    Rep == Record(sym: SymbolMeaning, cond: SExpression)
    import from Rep, SymbolMeaning

    id: Symbol == -"sig"
    signature?(tf: TForm): Boolean == id$% = id tf
    newTfSignature(sig: SymbolMeaning, cond: SExpression): % == per [sig, cond]
    symbolMeaning(sig: %): SymbolMeaning == rep(sig).sym

    (out: TextWriter) << (t: %): TextWriter == out << "{Sig" << "}"
    subst(tf: %, sigma: AbSub): % ==
        import from SymbolMeaning
        newTfSignature(subst(symbolMeaning tf, sigma), rep(tf).cond)

    typeInfo: TypeInfo == typeInfo(id,
                                    (tf: TForm): Boolean +-> false,
                                    (tf: TForm): List Export +-> [],
                                    (tf: TForm): SExpression +-> [sexpr(id$%), sexpression symbolMeaning(tf::%), rep(tf::%).cond])

    (a: %) = (b: %): Boolean == symbolMeaning a = symbolMeaning b

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

    typeInfo: TypeInfo == typeInfo(id$%,
                                   (tf: TForm): Boolean +-> false,
                                   (tf: TForm): List Export +-> [],
                                   (tf: TForm): SExpression +-> [sexpr(id$%), sexpression(arg(tf::%)), sexpression(ret(tf::%))])

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

    typeInfo: TypeInfo == typeInfo(id,
                                    (tf: TForm): Boolean +-> (inner := type(tf::TfDeclare); category?(typeInfo inner, inner)),
                                    (tf: TForm): List Export +-> [],
                                    (tf: TForm): SExpression +-> [sexpr(id$%), sexpr sym(tf::%), sexpression type(tf::%)])

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

    typeInfo: TypeInfo == typeInfo(id,
                                   (tf: TForm): Boolean +-> false,
                                   (tf: TForm): List Export +-> [],
                                   (tf: TForm): SExpression +-> cons(sexpr(id$%), [sexpression part for part in parts(tf::%)]))

#if 0
TfRecord: TFormSubType with
    newTfRecord: (List Symbol) -> %
== add

#endif

SymbolMeaning: OutputType with
    SExpressionOutputType
    PrimitiveType
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

    sexpression(tf: %): SExpression == [sexpr(-"Sym"), sexpr name tf, sexpression type tf]
    (a: %) = (b: %): Boolean == name a = name b and type a = type b

Export: OutputType with
    PrimitiveType
    SExpressionOutputType
    newExport: TForm -> %
    newExport: (TForm, TForm) -> %

    type: % -> TForm
    original: % -> TForm

    subst: (%, AbSub) -> %
    isCatExport: % -> Boolean
== add
    Rep == Record(tf: TForm, original: TForm)
    import from Rep, Symbol
    newExport(tf: TForm): % == per [tf, tf]
    newExport(tf: TForm, otf: TForm): % == per [tf, otf]
    type(e: %): TForm == rep(e).tf
    original(e: %): TForm == rep(e).original

    subst(e: %, sigma: AbSub): % == per [subst(type e, sigma), rep(e).original]

    isCatExport(e: %): Boolean == never

    (out: TextWriter) << (exp: %): TextWriter == out << "{S: " << type exp << "}"
    sexpression(e: %): SExpression == [sexpr(-"Export"), sexpression type e]
    (a: %) = (b: %): Boolean == type a = type b

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
    allCatParents: TForm -> List Export
    imports: TForm -> List SymbolMeaning
    asAbSyn: (Env, TForm) -> AnnotatedAbSyn
    canonicalise: AnnotatedAbSyn -> AnnotatedAbSyn
== add

    infer(sat: FnSatisfier, ab: AnnotatedAbSyn): TForm ==
        tf := infer1(sat, ab)
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
        --stdout << "inferApply: " << ab << " " << opType << newline
        argTypes := [infer(sat, arg) for arg in applyArguments(ab)]
        -- Do I need a satMap() with options?
        empty? argTypes and (category? opType or third? opType) => opType
        r: SatResult := satisfies(sat, newMulti argTypes, arg(opType::TfMap))
        --stdout << "SAT: " << r << newline

        --stdout << "Infer apply: " << ab << " " << opType << newline
        for argTf in args(opType::TfMap) repeat
            stdout << argTf << " " << declare? argTf << newline

        sigma: AbSub := [(sym(argTf::TfDeclare), arg) for arg in applyArguments ab for argTf in args(opType::TfMap) | declare? argTf]
        --stdout << "Infer sigma: " << sigma << newline
        retType: TForm := first rets(opType::TfMap)
        subst(retType, sigma)

    imports(tf: TForm): List SymbolMeaning ==
        import from Symbol, Export, TfSignature
        import from List Export
        import from SymbolMeaning
        self: AnnotatedAbSyn := boundSyntax tf
        none? self => error("can't find imports of unbound " + toString tf)
        sigma: AbSub := newSubst(-"%", self)
        sigs: Generator SymbolMeaning := (symbolMeaning(type(sigExport)::TfSignature) for sigExport in allCatParents tf | signature? type sigExport)
        [newSymbolMeaning(name syme, subst(type syme, sigma)) for syme in sigs]
        --[newSymbolMeaning(name exp, subst(type exp, sigma)) for exp in sigs]

    allCatParents(tf: TForm): List Export ==
        stdout << "Cat parents starts " << tf << newline
        import from TForm, Export
        expand(tf: TForm, seen: HashSet TForm): (List Export, List TForm) ==
            parentExports := [child for child in directCatParents tf | not member?(type child, seen)]
            myParents: List TForm := [type p for p in parentExports]
            (parentExports, [child for child in myParents])
        toDo: List TForm := [tf]
        seen: HashSet TForm := []
        exports: List Export := []
        while not empty? toDo repeat
            insert!(seen, first toDo)
            (exps, more) := expand(first toDo, seen)
            exports := append!(exps, exports)
            toDo := append!(more, rest toDo)
        stdout << "Cat parents done " << exports << newline
        exports

    asAbSyn(e: Env, tf: TForm): AnnotatedAbSyn ==
        import from TForm, List TForm, AnnotatedId, List AnnotatedAbSyn, TfMap, TfGeneral, TfMulti, Symbol, Partial TForm, SExpression
        helper(tf: TForm): AnnotatedAbSyn ==
            general? tf => syntax(tf::TfGeneral)
            map? tf => newApply(newId(newAnnotatedId(e, -"Map")), [helper(arg(tf::TfMap)), helper(ret(tf::TfMap))])
            multi? tf => newComma [helper part for part in parts(tf::TfMulti)]
            stdout << "Unknown conversion " << sexpression tf << newline
            newNone()
        ab := helper tf
        return ab

    canonicalise(ab: AnnotatedAbSyn): AnnotatedAbSyn ==
        import from AbSynOperations AnnotatedAbSyn
        fixApply(ab: AnnotatedAbSyn, recurse: AnnotatedAbSyn -> AnnotatedAbSyn): AnnotatedAbSyn ==
            import from List AnnotatedAbSyn
            id? ab => ab
            not apply? ab => recurse ab
            not id? applyOperator ab => ab
            not empty? applyArguments ab => recurse ab
            applyOperator ab
        map(fixApply)(ab)
