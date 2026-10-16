# Actual schedule selector prefix and array-construction components

This checkpoint proves the actual source components needed to close the complete schedule family:

- `SumHighTwoRanges.boxed_nodes` follows both real slice-iterator entries4..25 and33..57 with one accumulator across the boundary and derives canonical success/exact retained scheduleNodes at the same actual boxed point.
- `InitialVariantExact.source_success` proves actual variant helper success, canonicality of all four returned values and the retained source-order variant tuple.
- `InitialSelectorPrefix.same_boxed_success` derives the full source-order selector prefix through the full/rate multiplications, including all reads, variant branch and arithmetic. All12 returned registers are canonical and match the retained model at the same boxed point. No intermediate success/value equation is supplied as a premise.
- `AbsorptionCallback` and `AbsorptionLiteralExecution.source_success` derive the complete16-lane actual absorption array and every exact retained scheduleAbsorptionLiteral value.
- `InitialArrayCallback` and `InitialArrayExecution.source_success` derive the initial16-lane source segment: prepare full, add rate, prepare their sum, then run the actual callback for all lanes. It reuses the existing prepared constructor/state/multiplication correspondence and ArrayFromFnCopyStable loop proof. No16-step recurrence is newly unfolded.
- `ScheduleDomainArithmetic.source_success` derives actual note-first/domain/length checked chains using the exact pinned domain constants and the existing scalar multiplication theorem. A generic structural scalarEmbedding_nat lemma handles coefficient interpretation without reducing large numerals.
- `ScheduleFamilyFieldTransport` transports all32 mathematical schedule residuals between generic fields, preserving the variant, operation order, initial lanes and absorption lanes. It reuses previously checked high/low/contiguous-sum transport and old R0P models.

OccupancyGeneratedSlice and OccupancyExpectedBridge are the shared exact owners of the actual public/variant types and variant mapping. They are included with their existing green receipts to keep maintained dependency closure complete. The separate occupancy literal loop/full-list/enclosing proof is ongoing, not claimed here. Generated slices retain full declarations; isolated namespaces/module imports and stated helper adapters are the only changes recorded by manifests.

Still open for the complete schedule caller: domain/length coefficient-to-model composition, the two subtracting writes, the remaining absorption selector setup, whole-parent reconstruction and start0/start16 packing. These components are genuine implementation-to-model progress but are not the complete schedule family or accepted-spend theorem. The existing explicit library-model/derive boundary and candidate-to-release/artifact correspondence remain separate;100-bit implementation soundness and privacy are not claimed.

Focused proof repairs avoided concrete field normalization: explicit scalar/Fin identities connect actual indices, one generic monadic bind-if equality handles generated callback joinpoints, and tuple projections are reduced before matching model fields. NUC checks use the original resource/tactic limits. Independent capped jobs may overlap after checking aggregate reservations, with each job retaining its own evidence.

All included focused targets exited0 with zero process swaps. Every theorem axiom report contains only propext, Classical.choice and Quot.sound; declaration-only generated slices have no theorem reports. Exact source/import/object/revision/command/time/RSS/swap/cgroup evidence is retained. No unchanged broad replay was run.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `OccupancyGeneratedSlice` | 2.059 | 4077632 | 0 |
| `OccupancyExpectedBridge` | 1.758 | 4053576 | 1 |
| `SumHighTwoRanges` | 2.454 | 3969680 | 4 |
| `AbsorptionGeneratedSlice` | 1.261 | 2605372 | 0 |
| `AbsorptionCallback` | 1.889 | 3814152 | 2 |
| `AbsorptionLiteralExecution` | 2.291 | 3607040 | 1 |
| `InitialCallbackSlice` | 1.228 | 2603524 | 0 |
| `InitialArrayCallback` | 1.816 | 3738188 | 1 |
| `InitialArrayExecution` | 1.786 | 3601208 | 1 |
| `InitialVariantSlice` | 1.553 | 3965920 | 0 |
| `InitialVariantExact` | 1.623 | 3983472 | 1 |
| `InitialSelectorPrefix` | 2.048 | 4008492 | 1 |
| `ScheduleFamilyFieldTransport` | 3.775 | 3268172 | 6 |
| `ScheduleDomainConstants` | 1.024 | 2548872 | 0 |
| `ScheduleDomainArithmetic` | 1.323 | 2940136 | 2 |
