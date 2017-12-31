#include "aldor"
#include "aldorio"
#pile
import from SpadTypeLib

import from String
JList ==> java_.util_.List;
JIterable ==> java_.lang_.Iterable;

APPLY(id, rhs) ==> { apply: (%, 'id') -> rhs; export from 'id' }
JavaExceptionType: Category == with;

import
    Files: with
        readAllLines: Path -> JList String throw JavaExceptionType
        newDirectoryStream: Path -> JIterable Path throw JavaExceptionType
        isDirectory: Path -> Boolean
    Paths: with
        get: String -> Path

    Path: with
        APPLY(getParent, () -> %)
        APPLY(getFileName, () -> %)
        APPLY(toString, () -> String)
from Foreign Java "java.nio.file"

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
    Iterator: (T: with) -> with
        APPLY(hasNext, () -> Boolean);
        APPLY(next, () -> T);
from Foreign Java "java.util"

LibReader: with
    readJava: String -> List IndexedFile
    paths: String -> Generator String
== add

    readJava(s: String): List IndexedFile ==
        import from Files, IndexedFile, List Path, Path
        ll: List String := [paths(s)]
        [new(path + "/index.KAF") for path in paths(s)]

    paths(s: String): Generator String == generate
        import from Files
        stream: JIterable Path == newDirectoryStream(get(s)$Paths)
        iter: Iterator Path := stream.iterator()
        while iter.hasNext() repeat
            p: Path := iter.next()
            yield p.toString()
