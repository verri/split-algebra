# SplitAlgebra

Lean 4 development behind the paper "Split Safety for Tabular Data Handling: An
Algebra and a Completeness Theorem", by Paulo Giovani de Faria Zeferino, Filipe
Alves Neto Verri and Marcos Gonçalves Quiles.  Its thirteen modules check
every lemma, proposition and theorem of the paper; the table in the paper's
Mechanization section maps each statement to its declarations.

Library `SplitAlgebra`, Lean `v4.31.0`, Mathlib `v4.31.0`.  No `sorry`.

## Layout

- `SplitAlgebra/Core/{Defs,Ops}.lean`: tables, split/union, safety properties, operations
- `SplitAlgebra/SplitSafety.lean`: classification of each operation
- `SplitAlgebra/Laws.lean`: equational laws and key-move inverses
- `SplitAlgebra/Reshape.lean`, `Rectangle.lean`: pivot/unpivot and the rectangle facts
- `SplitAlgebra/Completeness/`: fiber maps, reindex and gather maps, derived verbs, attribute pivot, binary joins (`BinaryJoins.lean`)
- `SplitAlgebra/Leak.lean`: the classic leak, joining back the global mean, and mean imputation are not split invariant
- `AxiomCheck.lean`: fails if any declaration uses an axiom beyond `propext`, `Classical.choice`, `Quot.sound`

## Naming

Operations carry the paper's names (`unpivot` is the drop variant used in the
text; `unpivotKeepMissing` keeps missing cells; `pivotKey` spreads a key column,
`pivotAttr` an attribute; `leftJoin` and `innerJoin` take both tables).  Theorems
are `subject_property` (`aggregate_splitSafe`, `demote_not_preservesDisjoint`), and
equalities with a normal form are `x_eq_fiberMap`, `x_eq_reindexMap`,
`x_eq_gatherMap`.

## Building

Install [elan](https://github.com/leanprover/elan); it reads `lean-toolchain` and
fetches the right Lean version.  Then:

    make cache    # download the prebuilt Mathlib oleans (once)
    make build    # check every module
    make axioms   # run the axiom gate

Continuous integration runs the build and the axiom gate on every push.

## License

MIT, see `LICENSE`.
