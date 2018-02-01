#include "aldor"
#include "aldorio"
#pile

IndexedFile: with
    new: String -> %
    new: (String, HashTable(Symbol, SExpression)) -> %
    get: (%, Symbol, MachineInteger) -> SExpression
    keys: % -> List Symbol
== add
    Rep == Record(fname: String, values: HashTable(Symbol, Array ValPtr))
    ValPtr == Union(posn: MachineInteger, val: SExpression)

    import from Rep, ValPtr, Integer
    import from Array ValPtr

    new(name: String, tbl: HashTable(Symbol, SExpression)): % ==
        per [name, [(key, [[sx] for sx in sxl]) for (key, sxl) in tbl]]

    new(name: String): % ==
       file := per [name, table()]
       read file
       file

    keys(file: %): List Symbol == [keys rep(file).values]

    get(indexedFile: %, k: Symbol, n: MachineInteger): SExpression ==
        import from List Symbol
        import from File, SExpressionReader, SExpression, HashTable(String, ValPtr), Partial SExpression, Integer
        vp := rep(indexedFile).values.k.n
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
        posnOrPosnTimePair := retract sx
        posn := if cons? posnOrPosnTimePair then int first posnOrPosnTimePair else int posnOrPosnTimePair

        file := open(rep(indexedFile).fname)
        setPosition!(file, machine posn)
        dict := read(file::TextReader)

        rep(indexedFile).values := [ (if sym? first pair then sym first pair else -(str first pair), valptrs rest pair)
                                        for pair in retract dict]
        close! file

    local valptrs(sx: SExpression): Array ValPtr ==
        [(if int? sxc then [machine int sxc] else [sxc]) for sxc in sx]

