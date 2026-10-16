# Adaptive public recovery and compiled decoder

The strict initial-frame parser recovers public bytes from the address. The public-free initial walker reuses existing table-cell and prefix proofs. `EarlyPublicTotalCase.actual_first_cell` proves that the table-only selector recovers the actual public statement at rounds 0 through 26, including initial and reseed cases, for an arbitrary bounded-model prover. Public tag 2, message validity and collision/query premises remain explicit. `RawPublicSelectionLift` preserves density and the chronological table when lifting a bounded selector to unrestricted raw byte queries; it does not yet establish actual raw-run selection.

`RawLiteralCompiledDecoder` extends recorded-run decoder completion to the compiled prover, whose trace includes a repeated-verifier suffix. It uses exact table-before and follow-append lemmas. It still receives the actual public statement, and retains the underlying validity/parser premises.

Remaining obligations include actual raw public selection, late public recovery for rounds 27–32, source terminal acceptance, efficient extraction, and the final soundness instantiation. These proofs do not establish a complete 100-bit claim.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `RawPublicInitParser` | 1.506 | 3541680 | 3 |
| `InitialPublicWalk` | 1.649 | 3552000 | 1 |
| `InitialPublicWalkCells` | 1.685 | 3549900 | 1 |
| `InitialPublicWalkTrace` | 1.8 | 3533548 | 1 |
| `SemanticPublicSelection` | 1.693 | 3548820 | 1 |
| `EarlyPublicSelection` | 1.724 | 3542804 | 3 |
| `EarlyPublicExperiment` | 1.62 | 3547812 | 1 |
| `EarlyPublicSpecialCases` | 1.575 | 3545900 | 2 |
| `EarlyPublicTotalCase` | 9.726 | 3551124 | 2 |
| `RawPublicSelectionLift` | 1.615 | 3630544 | 2 |
| `RawLiteralCompiledDecoder` | 1.66 | 3644632 | 1 |
