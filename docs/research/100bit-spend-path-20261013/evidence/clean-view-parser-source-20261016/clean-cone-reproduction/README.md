# H caller cone with explicit library models

The caller source is the isolated owned-offset Shape candidate H, not deployed production source. CallerFuns preserves every retained generated body and omits only View.parse and its view_parse_probe wrapper, which referenced the opaque query-check template. The generator retains the omitted text and reconstructs the raw Funs exactly. CleanParameterizedParse retains the generated parent body with the existing explicit universal query function parameter and changes only its import to this caller cone. It introduces no query stub or axiom.

CallerStdModels provides concrete definitions for the five used Rust-library templates. Option.ok_or and Result.map_err reuse the earlier checked model/extraction pattern. Slice/Array eq/ne performs the pinned Rust as_array length split then delegates to the existing Aeneas Array comparison model. SliceIter.any reuses the earlier TraversalRuntime next-loop model; the pinned Rust specialized slice implementation also explicitly iterates next until a predicate hits. The generic Iterator.any.default external is not referenced by retained generated Funs and is omitted.

These are explicit library-model boundaries. This does not prove compiler correctness, arbitrary specialized PartialEq implementation equivalence, drop/unwind observations, the query checker, or production migration. Header comparisons at the actual caller use primitive U8. The later theorem must print only standard axioms and must retain its universal query helper rather than assume its success.

Pinned Rust source files, earlier Lean models and hashes are retained for provenance. No Lean build or proof success is claimed by this source package alone.
