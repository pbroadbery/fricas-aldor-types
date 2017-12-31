#include "aldor"
#include "aldorio"
#pile

IndexedFile: with
    new: String -> %
    new: (String, HashTable(Symbol, SExpression)) -> %
    get: (%, Symbol) -> SExpression
    keys: % -> List Symbol
== add
    Rep == Record(fname: String, values: HashTable(Symbol, ValPtr))
    ValPtr == Union(posn: MachineInteger, val: SExpression)

    import from Rep, ValPtr, Integer

    new(name: String, tbl: HashTable(Symbol, SExpression)): % ==
        per [name, [(key, [sx]) for (key, sx) in tbl]]

    new(name: String): % ==
       file := per [name, table()]
       read file
       file

    keys(file: %): List Symbol == [keys rep(file).values]

    get(indexedFile: %, k: Symbol): SExpression ==
        import from List Symbol
        import from File, SExpressionReader, SExpression, HashTable(String, ValPtr), Partial SExpression, Integer
        vp := rep(indexedFile).values.k
        vp case val => vp.val
        file := open(rep(indexedFile).fname)
        setPosition!(file, vp.posn)
        valsx := read(file::TextReader)
        failed? valsx => error("Failed to read " + toString k)
        vp.val := retract valsx
        vp.val

    local read(indexedFile: %): () ==
        import from File, Symbol, SExpressionReader, SExpression, HashTable(Symbol, ValPtr)

        file := open(rep(indexedFile).fname)
        sx: Partial SExpression := read(file::TextReader)
        failed? sx => error "failed to read position in " + rep(indexedFile).fname
        close! file

        posn := int retract sx

        file := open(rep(indexedFile).fname)
        setPosition!(file, machine posn)
        dict := read(file::TextReader)
        close! file

        rep(indexedFile).values := [ (-(str first pair), valptr rest pair) for pair in retract dict]

    local valptr(sx: SExpression): ValPtr ==
        i0 := first sx
        i1 := first rest sx
        if not int? i1 then [i1] else [machine int i1]

testIndex(): () ==
    import from Symbol, IndexedFile, SExpression
    f := new("/home/pab/Work/fricas/build/src/algebra/A1AGG-.NRLIB/index.KAF")
    stdout << get(f, -"abbreviation") << newline

--testIndex()
