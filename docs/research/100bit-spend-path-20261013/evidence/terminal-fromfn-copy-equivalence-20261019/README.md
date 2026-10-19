# Stable terminal callback and extracted copy-helper equivalence

A callback that preserves its captured state yields the same ordered array in the explicit state-threaded from_fn model and in the already extracted array_from_fn_copy helper. The concrete terminal selector is proved stable and selects claims[i/28][i%28] for all 84 reached indices, skipping column 28 in each 29-value row. Its helper/model equivalence is a theorem, rather than a desired output-array premise.

This does not prove Rust core::array::from_fn or identity between the source-adapted callback slice and the complete generated current terminal method. The current Rust source migration candidate and its subsequent Aeneas extraction remain separate evidence. No production code is changed by this packet.

Three focused Lean 4.32 checks exited zero; their printed axiom reports contain only standard Lean axioms. Exact sources, objects, imports, revisions, commands, wall times, peak RSS and zero process swaps are recorded. Existing ArrayFromFnCopyStable and ArrayFromFnCopySlice sources/objects are reused, without rebuilding their graph. This is working evidence, not the unified release replay or complete private-spend theorem.
