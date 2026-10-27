# Inversion continuation — 2026-10-27

**Target not yet established. V380-inversion OPEN → OPEN. No endpoint or deployment premise removed.** No checked protocol witness-pair counterexample was found. The bound, simE, complete observer and capped three-field trust list are unchanged. Shipped code was not edited.

Branch `codex/pv-inv2-20261027`; base `4bdd2679c847a2b8354fa4c2fa9ea941484984e0`. Stage history is in HISTORY.txt; the complete range is `git log --oneline 4bdd2679c8..HEAD`. Read-only RunJoin12 branch pin and its status are retained; no installed-caller theorem is inferred from its candidate runtime.

## Bindings and per-site result

| Site/family | Checked result | Remaining P obligation |
|---|---|---|
| LogUp producer, logup.rs:200 | SourceProducerJoin.source_inverse derives raw 16-limb tuple reads, compression, canonical nonzero subtraction, false QM31 zero predicate and successful extracted inverse; ActiveRegistry provides all local endpoint-active/tag bounds. | Actual dynamic native enumeration = source descriptors; actual compiled.trace banks = same headline trace; installed arithmetic/caller identification. |
| LogUp consumer, :213 | SourceConsumerJoin.source_inverse proves the corresponding consumer result. | Same installed P bindings. |
| Native interleaved row builder, pair_forest_trace.rs:636–665 | RegistryPacking/RegistryZeroEvent and DecodedRun/Safety preserve first-zero-slot indexing, zero-weight overwrites, producer/consumer order and successful allocation. No equality of native dynamic slots with terminal static slots is assumed. | P_rows/P_reached identify actual extracted row/state/operand lists, including error ordering. |
| Native preguard, host_semantic.rs:273–357 | PreGuard.source_equation identifies the model four-slot active-row scan with NoPole. GuardedRegistry.no_zero and GuardedNativeTests.tests_false exclude helper zero after interpreted guard success. | P_static_values, P_active_masks, P_guard_equation and the installed call order. The guard reads compiled.trace, not noised commitment C1. |
| Active masks | All 136 model links have both endpoints active and tags < p. MaskPartition supplies symbolic OR composition. MaskChunk0–2 check block masks 0–47. | Blocks 48–63 have no successful whole-module receipt. J43697/43698 failed recursion depth; the latter proves more prefixes but is not accepted. Pending contains the exact failed replacement and generic/order/bridge drafts. No recursion or heartbeat cap was raised. |
| QM31→CM31→M31 norms | TripleNorm and PackedNormSafety compose the existing extracted norm arithmetic for reached native slots. InverseList/PackedInverseList prove successful inverse lists with canonical outputs and false whole-value zero verdicts. | Native caller/operand association; full limb/address/latency observations are not determined by these verdicts. |
| host_sumcheck.rs:30 interpolation | Predecessor initializer/nonzero-denominator proofs reused unchanged. | Installed bounded caller/source identification. |
| Circle/transcript fallback | Predecessor ±i singularity and subfield exclusion facts reused unchanged. | Same-coupling challenge/fallback trace law. Challenge-only provenance alone is insufficient. |
| z4 certificate pivots, geometry and half-pole | Predecessor pivot-control/domain facts reused; new Kani control slices do not prove certificate arithmetic. | Native challenge-record/geometry association and original joint observation law. |
| Sentinel constructor and total inv_r aliases | Predecessor guarded sentinel success/total exponentiation facts reused unchanged. | Constructor retry/native caller and operand-latency observation law. |

Source anchors/hashes: source-pins.json; exact unresolved equations: OBLIGATIONS.md. Native references are explicitly labelled as bounded structural references. They are not silently promoted to installed Aeneas extractions. STAGE1.md/STAGE2.md distinguish their conditional claims.

## Containment theorem and unchanged charge

`R1Z.PV_Inv_CouplingPole.contained` concludes the **literal existing** `R0Z.HvzkV.poleBad P h (VR1 h) ab adv x w (toCoins u)` from a reached registry zero and `P` at the **same attempt**. Its bank trace is exactly `h.build w`; lambda/chi are sem0/sem1 of `ab.draw adv x (toCoins u k)`. Hypotheses are explicit native registry/bank/run equations. The installed headline must supply its original coupling's `toCoins`; an unrelated sampler is not substituted. `HeadlinePole.attempt_contained` supplies the corresponding existing `attemptBad`.

`HeadlineCharge.mass_at_existing_term` proves the mathematical union's mass is at most **`8 * (4096 / ((2^31−1)^4−1))`**, exactly the final summand of `PrivacyR1Final.modelError` retained in `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`. It reuses the pole-set mass and existing Sem1Uniform law and charges all packed slots/weights/banks at once. It is not a new freshBudget, seed, fuel, failure or 16/2^486 charge.

Crucial limitation: actual `poleBad` includes `P ∧ ¬VR1`; the preguard occurs before the later public certificate check. A numeric bound on a larger `¬NoPole` event does not place it in the existing union. Interpreted preguard success rules out reached helper inversion zeros outright, but its rejection and complete comparison observations still need the existing same-coupling union/observer law. No failure is silently absorbed and no union is enlarged.

## Receipts and audit

[INDEX.md](INDEX.md) links every receipt; [SUMMARY.json](SUMMARY.json), [AUDIT-MANIFEST.json](AUDIT-MANIFEST.json) and [AXIOMS.md](AXIOMS.md) pin the final sources and declarations. Each Lean receipt records target, exit, wall time, peak RSS, swaps, source revision/hash, dependency fingerprint and full printed axiom lines. Logs and failed source snapshots remain in each J directory. Kani receipts have the same resource/source metadata; #print axioms is N/A.

- **100 charged Lean attempts: 85 pass, 15 fail.** Ordinary J43600–J43698 used 99 unique IDs, including two local unchanged-input refusals J43644/J43652 (zero charged). Final audits used only reserved J43897–J43899. No ID reused.
- **6/6 Kani runs pass**, solely bounded control/indexing slices in CONTROL-SLICES.md. No chained arithmetic SAT gate, inverse stub, or whole-function equivalence claim. The two-slot harness reports one unreachable unsupported construct, not a reachable assumed operation.
- Final accepted sources: **82 proof modules plus 3 audits; 181 theorem declarations**, all final axiom sets subsets of `propext`, `Classical.choice`, `Quot.sound`. Failed elaborations' `sorryAx` outputs are not accepted. Final source scan finds no forbidden proof mechanism or resource override.
- J43899 `R1Z/PV_Inv_AuditResume3`: **exit 0, wall 0:01.64, peak RSS 4,126,320 KiB, swaps 0**, revision `5d19e0d63f9233f1aae4a2736a853a9ae08ee89d`, with exact source hash in its receipt. Maximum Lean RSS: **4,129,856 KiB**; swaps 0 throughout.
- Every scope used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000; at most one scope at a time. The existing reservation barrier ran before source transfer, with retained diagnostics. Private paths used the existing env-J driver read-only; no shared source/object, launcher or driver was rewritten. Read-only cache references and env-J rebuild authority are recorded. No local Lean compile, cold dependency build, cap increase, memory-pressure rerun or unchanged full regression. Private compiled scratch was removed after recording all 85 object hashes/sizes (own-object-hashes.json and cleanup.json); shared caches remain intact.
- Both generated preflights pass `--check`. Mask J43691's direct 272-row fold was replaced by symbolic `MaskPartition`, tested before affected chunks. Tail blocks 51–63 use named small chunk-contribution equations in the generator. The remaining tail failure is pending; no full-mask identity is credited. This is a focused union/axioms audit, **not** a deployed frozen-manifest release replay.

## Premises and next deliverable

Before/after: V380-inversion **OPEN → OPEN**; all predecessor L2 whole-row obligations retained. Endpoint/deployment premises removed **0**, added **0**, weakened **0**; trust items added **0**. Local `P_*` propositions name existing missing native bindings; they are not new endpoint assumptions or trust fields. No shipped-source, bound, simE, observer, release pin or wallet/key change occurred.

Next: prove the native dynamic enumerator/descriptor equality and identify selected installed compiled.trace/bank inputs on the read-only RunJoin12 caller. Complete the tail mask proof by splitting the final OR aggregation (latest failures occur after the eight-row contribution lemmas), then instantiate the preguard/helper equations on the original headline coupling and prove its complete observed guard/zero-event law in the existing bad union. If that reveals an uncharged witness-dependent zero, construct the checked witness-pair counterexample and stop for the owner. No such counterexample is claimed here.

Stopped on exhaustion of both requested budgets. **Target not yet established.**
