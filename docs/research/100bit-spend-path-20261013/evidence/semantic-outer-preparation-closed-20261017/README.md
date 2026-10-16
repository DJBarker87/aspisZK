# Complete semantic caller: outer loop and same-preparation public bounds

The endpoint is `AspisR1.SemanticPackedSixFamiliesActualPreparation.actual_semantic_packed_of_preparation` in maintained module `SemanticPackedSixFamiliesActualPreparationClosed`. It proves successful execution and canonicality of all24 outputs of the bounded-carry semantic_packed source candidate, and exact agreement of each output with the retained packed lane relation. The public value in that relation is computed from the same preparation statement. There is no supplied outer-loop, branch, family, or intermediate arithmetic success premise, and no separately supplied public-field canonicality premise. Point/opening canonicality and the same successful boxed selector call remain inputs.

This closes the `OuterSound` obligation retained explicitly in the prior `semantic-six-family-source-20261017` checkpoint. `SemanticPackedOuterClosed.outer_sound` supplies it from an execution theorem for the actual20-level iterator. `TerminalDigestPublicLoopFuel` proves a fuel invariant for the exact source range iterator, preserving the same live snapshot and matching the retained frontier prefix at every step. Branch conditions, target selection, array reads, row addressing, bit tests and binding arithmetic are derived from the source inputs, rather than supplied as successful branch executions. Canonicality of the raw snapshot frontier is a necessary premise of this component: its underlying U32 carrier alone does not prove the M31 bound.

The preparation chain discharges that premise and all other used public bounds. `PreparationPublicFieldsCanonical` derives checked serializer canonicality from actual preparation public_transcript success. `TerminalSemanticPublicPreparationCopy` proves projection equality for the exact constructor field copies after statement projection. `TerminalSemanticPublicFieldsCanonical` proves bounds for those copies, including variant shape (private-transfer amount is absent; withdrawal recipient is absent). `TerminalSemanticPublicDigestCanonical` packages digest, snapshot, next-frontier, asset and optional amount bounds, and the final corollary handles the absent amount as zero. Omitted metadata in the reverse projection uses placeholders only to prove equality of the raw public projection: no equality of whole SDK/public objects or custody/reachability theorem is claimed.

The serializer adapter changes only generated discriminant reader instance names for three types (`Error`, `CompiledVariant`, `r0.Public`) to qualified names. Constructor order is preserved and the inverse map restores original Types bytes. Its Funs bytes are unchanged. Exact original/adapted source and inverse mapping are included. Final digest canonicality and six-family receipts use the coherent joint inner-digest chain and canonical TerminalLiftM31Exact owner; historical separately compiled duplicate owners are not used for the endpoint. Imported source/object pins are recorded in the exact receipts.

The bounded-carry Rust implementation remains a reviewed, separately extracted source candidate. Production Rust is unchanged at this checkpoint; full modified-crate re-extraction, release/runtime correspondence, complete composition caller binding, caller reachability/custody, concrete transcript/sampler refinement, privacy and the final100-bit accepted-spend theorem remain open. This result is a completed semantic component, not a completed protocol security proof.

All listed targets exited0 in focused Lean4.32 NUC jobs under MemoryHigh4GiB/MemoryMax6GiB/MemorySwapMax0, with no dependency rebuild and only standard axioms. Exact commands, source revision, source/object/import pins, wall time, peak RSS, swap and axiom reports are retained in each receipt. These are the existing successful focused runs; no unchanged regression was repeated for packaging. A final coherent frozen-manifest replay remains due after the enclosing caller chain is assembled.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `TerminalDigestBranchBits` | 1.576 | 3729016 | 1 |
| `TerminalDigestPublicBranchModel` | 1.57 | 3971852 | 1 |
| `TerminalDigestFrontierTarget` | 1.688 | 4037192 | 1 |
| `TerminalDigestBindingFrontierStep` | 1.721 | 3979196 | 1 |
| `TerminalDigestPublicRow` | 1.92 | 4017380 | 2 |
| `TerminalDigestPublicRowExtended` | 1.687 | 4017332 | 3 |
| `TerminalDigestPublicRowAddressOps` | 1.823 | 4016256 | 1 |
| `TerminalDigestPublicTargetActual` | 2.158 | 4044008 | 1 |
| `TerminalDigestPublicBranchCall` | 2.193 | 4003028 | 1 |
| `TerminalDigestPublicBranchRun` | 2.038 | 4055044 | 1 |
| `TerminalDigestPublicLoopFuel` | 1.948 | 4055368 | 2 |
| `SemanticPackedOuterClosed` | 1.81 | 4072064 | 2 |
| `PreparationPublicFieldsCanonical` | 3.494 | 3794368 | 1 |
| `TerminalSemanticPublicPreparationCopy` | 1.761 | 4062452 | 5 |
| `TerminalSemanticPublicFieldsCanonical` | 2.613 | 4048808 | 4 |
| `TerminalSemanticPublicDigestCanonical` | 1.791 | 4071452 | 1 |
| `SemanticPackedSixFamiliesActualPreparationClosed` | 1.822 | 4102304 | 1 |
