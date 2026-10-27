# Inversion continuation 3 — 2026-10-27

**Target not yet established. V380-inversion OPEN → OPEN. No endpoint/deployment premise removed.** No checked valid witness-pair counterexample was found. Shipped code, release pins, bound, simE, D159 observer and capped three-field trust list are unchanged.

Branch: `codex/pv-inv3-20261027`; starting revision in base.txt. Path-limited stage history through the pre-audit commit is in HISTORY.txt; complete history including the final audit commit is `git log --oneline $(cat evidence/pv-inv3-20261027/base.txt)..HEAD`. No push or merge.

## Per-site status

| Site/family | Proved or reused | Still open |
|---|---|---|
| Active masks, blocks 48–63 | All 16 blocks and tail range bridge compile; full 64-block MaskTable.source_equation passes. Named small contribution proofs replace failing reduction. | Installed dynamic schedule/registry identification. |
| Sorted/dedup mask construction | MaskFold / MaskRowFold / MaskRowEquation prove raw OR-fold equality from equality of member row sets; duplicates/order do not change the mask. NativeMaskEquation connects the model table conditionally on P_registry. | Actual successful native schedule projection and sort/dedup member-set equations; Rust u16/source association. |
| LogUp producer :200 and consumer :213 | Predecessor canonical tuple/compression/inverse arithmetic reused. Required RawBankRead/List/Tuple and NativeTupleJoin closure replayed successfully. | Native dynamic registry, selected banks, challenges, installed arithmetic and exact caller/operand association. |
| Dynamic two-slot packing, pair_forest_trace.rs:636–665 | Predecessor packing/zero-event closure replayed. Kani confirms first-zero-slot overwrite behavior; static slots are not equated with dynamic slots. | Installed rows/reached/error-order equations. |
| Preguard, host_semantic.rs:273–357 | GuardAttempt / GuardCoupling place P-qualified interpreted rejection in existing poleBad. GuardTraceShape / Pair / ObservedCoupling prove fixed whole-value Boolean traces outside it, on the original coupling parameter. GuardedRegistry.no_zero replayed. | Actual static arrays, masks, banks and call order; P-false guard outcomes; complete limb/index/address/latency observation law. |
| QM31/CM31/M31 norms | Predecessor exact arithmetic/nonzero norm and successful inverse-list proofs retained. | Actual reached operand/caller and latency association. |
| Interpolation, host_sumcheck.rs:30 | Predecessor initialization/nonzero denominator results reused. | Installed bounded caller/operand identification. |
| Circle/transcript fallback | Predecessor singularity/subfield exclusion facts reused. | Same-coupling challenge/fallback trace law. |
| Certificate pivots, geometry, half-pole | Predecessor domain/pivot control facts reused. | Native challenge-record/input identification and joint observation law. |
| Sentinel constructor, total inv_r | Predecessor guarded success/totality facts reused. | Actual retry/caller and operand/latency observation law. |

Exact remaining P equations and shipped locations are in OBLIGATIONS.md. RunJoin12 was read-only, pinned and rechecked at `0a6a5428a8726c578f6076e8da9bdbdb4e8f1a8d`; its published status credits **no R_shipped or selected records identification**. No candidate runtime is promoted to installed execution, and no missing proof is added to T.

## Containment and charge

The predecessor `PV_Inv_CouplingPole.contained` still places a reached registry zero with P at the **same attempt** in the literal existing `R0Z.HvzkV.poleBad`, with banks identified to `h.build w` and lambda/chi from that coupling's `ab.draw`. New `PV_Inv_GuardCoupling.reject_contained` does the corresponding job for the interpreted guard rejection. Neither omits P, changes the coupling, substitutes a sampler, nor enlarges the bad union.

`PV_Inv_HeadlineCharge.mass_at_existing_term` retains exactly **`8 * (4096 / ((2^31−1)^4−1))`**, the existing modelError summand. No additional seed/fuel/freshBudget/scan/failure charge is introduced. Its numerical bound alone is not native event containment.

The guard precedes public_check. Reaching rejection does not establish P. Equal successful Boolean lists do not establish equal limb tests, addresses, allocation paths or latency; OBSERVATION.md enumerates each unresolved outcome. The complete inversion observation law is **not proved**. No model-only differing limb prefix is passed off as a protocol counterexample.

## Validation and stopping condition

- **100/100 charged Lean attempts: 97 pass, 3 corrected elaboration failures.** IDs 43900–43996 and reserved audit IDs 44197–44199 used exactly once. No reservation refusals or unchanged reruns. IDs 43997–44196 unused. The cache-restoration dependency compiles are charged; no unchanged full regression was run.
- **6/6 Kani runs pass**, only bounded control/indexing slices. K05/K06 warn about unreachable unsupported constructs (3 and 8 unreachable checks); no reachable operation is assumed and no arithmetic equivalence is claimed. CONTROL-SLICES.md gives scope, source anchors and exact limitations.
- All **31 new modules (28 proof modules and 3 audits)** have successful final receipts. The focused audit covers every new theorem; accepted axiom sets are subsets of `propext`, `Classical.choice`, `Quot.sound`. Failed elaborations' sorryAx output is retained as failure evidence, never accepted. Final source scan has no forbidden mechanism or resource override.
- J44197 `R1Z/PV_Inv_AuditInv3Masks`: exit 0, wall 0:03.26, peak RSS 3,291,948 KiB, swap 0; 576 printed axiom lines.
- J44198 `R1Z/PV_Inv_AuditInv3Bindings`: exit 0, wall 0:02.74, peak RSS 3,288,432 KiB, swap 0; 10 printed axiom lines.
- J44199 `R1Z/PV_Inv_AuditInv3Coupling`: exit 0, wall 0:03.65, peak RSS 3,574,640 KiB, swap 0; 12 printed axiom lines. All three audit receipts pin revision `8dfae8e4807b2f9e0aca3775c209f20b756e3b73` plus exact source hashes/dependency fingerprints. Maximum Lean RSS across all attempts: 4,081,176 KiB; swaps 0 throughout.
- Every scope uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0; private scopes TasksMax=64 and Lean -M7000. At most one capped scope at a time. Reservation diagnostics precede source transfer. No local Lean compile, cold package build, cap increase or arithmetic Kani retry.
- All three generator preflights pass --check. Shared source audit confirms byte equality with rebuild-resolved sources for Copy, CopyConstants, CopyRegistry, HvzkV, PoleMassR1 and ReadBudgetR1. Authority is the env-J rebuild record, not the obsolete import pin table. No shared source/object or launcher was written. Private compiled scratch was removed after retaining all 97 object hashes/sizes; source/evidence remain, borrowed shared artifacts untouched.
- INDEX.md links every receipt; SUMMARY.json, AUDIT-MANIFEST.json, AXIOMS.md, generator-preflight.json, shared-source-audit.json, own-object-hashes.json and cleanup.json retain reproducible metadata. This is a focused closure/axioms audit, **not a deployed frozen-manifest release replay**.

## Premises and next deliverable

Before/after: V380 **OPEN → OPEN**. Endpoint/deployment premises removed 0, added 0, weakened 0; T fields added 0. The tail model mask gap and OR-order algebra are closed. Native enumeration, bank/caller/record bindings and complete observation law remain proof obligations, explicitly named rather than hidden in T.

Stopped on exhaustion of both budgets, not on a counterexample. Next: a checked native dynamic registry/schedule refinement proving P_registry and the successful endpoint row-set equation, preserving order, tags, bank descriptors, tuple offsets and weights. Then instantiate banks/challenges from RunJoin12 when shipped records identification is published, and prove P-false guard outcomes and every limb/address/latency outcome simulatable or in the existing bad union on the original headline coupling. **Target not yet established.**
