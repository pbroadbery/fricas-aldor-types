#include "aldor"
#include "aldorio"
#pile

IndexedFile: with
    newIndexedFile: String -> %
    get: (%, Symbol) -> SExpression
    keys: % -> List Symbol
    newIndexedFile: (String, HashTable(Symbol, SExpression)) -> %
== add
    Rep == Record(fname: String, values: HashTable(Symbol, ValPtr))
    ValPtr == Union(posn: MachineInteger, val: SExpression)

    import from Rep, ValPtr, Integer

    newIndexedFile(name: String, tbl: HashTable(Symbol, SExpression)): % ==
        per [name, [(key, [sx]) for (key, sx) in tbl]]

    newIndexedFile(name: String): % ==
       file := per [name, table()]
       read file
       file

    keys(file: %): List Symbol == [keys rep(file).values]

    get(indexedFile: %, k: Symbol): SExpression ==
        import from List Symbol
        import from File, SExpressionReader, SExpression, HashTable(String, ValPtr), Partial SExpression
        vp := rep(indexedFile).values.k
        vp case val => vp.val
        file := open(rep(indexedFile).fname)
        setPosition!(file, vp.posn)
        valsx := read(file::TextReader)
        vp.val := retract valsx
        vp.val


    local read(indexedFile: %): () ==
        import from File, Symbol, SExpressionReader, SExpression, HashTable(Symbol, ValPtr)

        file := open(rep(indexedFile).fname)
        sx: Partial SExpression := read(file::TextReader)
        failed? sx => error "failed to read " + rep(indexedFile).fname
        posn := int retract sx
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
    f := newIndexedFile("/home/pab/Work/fricas/build/src/algebra/A1AGG-.NRLIB/index.KAF")
    stdout << get(f, -"abbreviation") << newline

--testIndex()
