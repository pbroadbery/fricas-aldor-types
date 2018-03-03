# fricas-aldor-types

Very simple type system for aldor.

This supports extracting types from daase and nrlib files and discovering exported operations and parents of types.

There is very little type inference - it is assumed that all types are well-formed.

ToDo:
- Conditionals
- Argument checking

Note that the source code is very raw, and I have not cleaned up various experiments.
Most of the interesting code is in the types/index directory.

axiomshell.as shows how aldor and java types interact.

