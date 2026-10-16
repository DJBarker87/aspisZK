# Actual indexed 33-cell value-lane multiplication

SelectorValueLaneIndexedLoop3 proves the actual generated candidate index loop succeeds from index zero, preserves canonicality and decodes every cell to selector times its original residual. The proof uses a symbolic fuel invariant and actual checked QM31 multiplication/array read/update/increment, not an assumed mutable iterator contract or concrete 33-step kernel normalization.

PreweightedGroupUpdate factors the actual generated loop body and proves the complete per-group array read/pack/add/write succeeds, preserves canonicality, has the exact mathematical result in the updated cell, and leaves every other cell unchanged. The outer traversal theorem remains separate.

PreweightedLoopSlice contains the exact generated outer add_preweighted loop/wrapper declarations for the next dependent proof; its declaration check does not prove traversal correctness. Exact generated candidate input/output provenance is retained in terminal-indexed-source-candidate-20261016.

Focused NUC Lean4.32 checks, exit0, zero swaps, standard theorem axioms only. No complete add_value_lanes caller, terminal-source implication, release equivalence or runtime claim is made.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `SelectorValueLaneIndexedLoop3` | 2.256 | 3820872 | 2 |
| `PreweightedLoopSlice` | 1.329 | 2605120 | 0 |
| `PreweightedGroupUpdate` | 1.698 | 3006912 | 2 |
