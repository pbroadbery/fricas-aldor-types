#include "aldor"
#include "aldorio"
#pile

IndexedFile: with
    newIndexedFile: String -> %
    get: (%, Symbol) -> SExpression
    keys: % -> List Symbol
== add
    Rep == Record(fname: String, values: HashTable(Symbol, ValPtr))
    ValPtr == Union(posn: MachineInteger, val: SExpression)

    import from Rep, ValPtr, Integer

    newIndexedFile(name: String): % ==
       file := per [name, table()]
       read file
       file

    keys(file: %): List Symbol == [keys rep(file).values]

    get(indexedFile: %, k: Symbol): SExpression ==
        import from List Symbol
        import from File, SExpressionReader, SExpression, HashTable(String, ValPtr), Partial SExpression
        stdout << "Get: "  << k << " "  << keys indexedFile << newline
        for (ak, av) in rep(indexedFile).values repeat stdout << "K: " << ak << " " << (k = ak) << newline
        vp := rep(indexedFile).values.k
        vp case val => vp.val
        file := open(rep(indexedFile).fname)
        stdout << "Posn is " << vp.posn << newline
        setPosition!(file, vp.posn)
        valsx := read(file::TextReader)
        vp.val := retract valsx
        vp.val


    local read(indexedFile: %): () ==
        import from File, Symbol, SExpressionReader, SExpression, HashTable(Symbol, ValPtr)

        file := open(rep(indexedFile).fname)
        stdout << "Reading " << rep(indexedFile).fname << newline
        sx: Partial SExpression := read(file::TextReader)
        failed? sx => error "failed to read " + rep(indexedFile).fname
        posn := int retract sx
        stdout << "Read position " << posn << newline
        setPosition!(file, machine posn)
        dict := read(file::TextReader)
        close! file
        stdout << "read dictionary: " << dict << newline

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
