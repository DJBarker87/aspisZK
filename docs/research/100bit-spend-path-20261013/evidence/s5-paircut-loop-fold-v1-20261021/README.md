# PairCut callback fold proof

This packet records a checked callback-parameterized finite push trace for the emitted PairCut byte-products operation sequence. `callback_push_trace_total` consumes an explicit index list, per-index successful field and scratch reads, their canonicality bounds, and the initial count-indexed accumulator invariants. It returns the ordered concrete EbyK push trace, final invariants, and exact count increase.

The one-step body adapter retains read → scratch index → push → Continue ordering. The iterator range transition is not yet connected to a complete actual PairCut loop; the PairCut external `weights.field` source symbol is also not equated with the retained decoder. No `FunsExternal` axiom is used in the checked theorem.

The callback dependency source is reconstructed from its immutable successful launch snapshot and its SHA matches that producer receipt. It is copied here rather than using the later mutable working copy, which contains an uncompiled added theorem. Imported OLean files are not included.
