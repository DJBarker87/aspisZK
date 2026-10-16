# Actual literal transcript state and first-read ordering

These proofs connect actual literal protocol sampler outputs, next transcript states, frame prefixes, and oracle-read membership. They prove ordinary frame-to-advance ordering and a generic raw-byte query-chain ordering lemma using the single existing raw collision event. The initial-round advance-read theorem is also checked.

The all-33-frame strict ordering theorem still needs the initial/reseed/query adjacency compositions. In particular, the query sampler's returned state is selected by its stop rule and is not assumed to be the eighth advance. These focused predecessors do not replace those remaining compositions with ordering assumptions.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `RawCutLiteralStateSuccessor` | 1.642 | 3587540 | 4 |
| `RawCutLiteralSamplerOrder` | 2.161 | 3651256 | 1 |
| `RawCutLiteralTranscriptSuccessor` | 1.5 | 3621316 | 1 |
| `RawCutLiteralNextFrame` | 2.026 | 3653944 | 3 |
| `RawCutLiteralQueryOrder` | 0.88 | 1845864 | 1 |
| `RawCutLiteralInitialAdvanceRead` | 1.841 | 3649944 | 1 |
