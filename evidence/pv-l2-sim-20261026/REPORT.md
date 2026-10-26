# L2 continuation report, 2026-10-26

Branch: `codex/pv-l2-sim-20261026`; continuation base: `36717b11ae`.
Proof/evidence commit: `f26a2808ad`. [Commit history](HISTORY-CONTINUATION.txt).
The [predecessor report](REPORT-predecessor.md) preserves the previous allocation and results.

**No premise was removed from `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` or its deployment conditions. The privacy target is not established.** The fresh allocation is exhausted: 100 Lean attempts (J21900–J21999, 59 successful) and 20 Kani runs (z01–z20, 17 successful). These are separate from the predecessor's 100/20. This report counts complete ledger obligations, not helper theorems: CLOSED 0, REDUCED 0, OPEN 19.

## Proved results and remaining association obligations

### F3: failure-preserving source, full L1 attempts, ROM carrier

`PV_L2_F3FullSource.observed_erases` identifies the rich producer's value/count projection with the predecessor's `F3SourceJoint.sourceObserved`. The outer read record remains present when the result is `None`; checked failure and divergence preserve their already executed prefix. The second stream runs only after the first succeeds.

`PV_L2_F3FullRetry.full_l1_erases` projects the rich retry runner onto the FULL `SideChannelL1AttemptRecord` runner, including rejected attempts, stopping attempts and all state updates. Each attempt carries the full L1 `Attempt`, mask/entropy read lists and ordered ROM entries. `rejected_rom_prefix` retains the rejected attempt's supplied ROM prefix. This is a carrier and callback theorem: the supplied list has not been identified with the actual adaptive ROM execution.

`PV_L2_F3AttemptSource.complete_l1`, `source_projection` and `owned_projection` fill each attempt's read lists using the owned producer and preserve its complete L1 and endpoint decoder projections. `PV_L2_F3PrefixBounds` proves read bounds, actual extracted-next answers, request bounds, failed/diverging reads and exhaustion. The bound is `16 * L + r`, covering unsuccessful prefixes as well as successes.

`PV_L2_F3SeedFrames.next_reseed` proves that the actual extracted next-word operation commutes with reseeding in the finite counter backend: values, cache, counters and errors are unchanged while the seed frame is restored. `PV_L2_F3SeedPrefix.transport` extends this to the entire producer, mapping every read frame and retaining the same optional value/count result, including failed and divergent prefixes. This backend's block hash ignores the seed; this is not adaptive-ROM equivalence, a seed independence law, or witness absorption.

### SAME coupling, explicitly conditional

`PV_L2_Premises.PV_L2_Premises` has 19 explicit Prop fields, exactly one per row listed below. Each field asserts equality of that row's observable on the EXISTING `RunJoin.cp` outside `ProverCommitFuelJoin22.bad old queries`. `V366` asserts equality of the whole rich run. No field is hidden in an observer definition. `extend` retains `join.cp` definitionally; `same_coupling` proves that equality. `rows_agree` combines the remaining 18 row fields.

`PV_L2_PremisesBound.joint_test_bound` bounds a bounded test of the full `(view, richRun, allRows)` with the original charge once:

```
eventMass (fun m => ∃ i, old i m)
  + ProverCommitSeedEvent19.budget q
  + ProverCommitFuelMass22.charge
```

It is conditional on all 19 fields. It neither proves those fields nor supplies source-to-unchanged-`simE` absorption of the whole record. `PV_L2_HeadlineJoint.original_refinement` extracts the actual headline RunJoin from the endpoint's RustRealRefinement; `agreement_exact` exposes that join's original `realBad`, seed and fuel union. Direct specialization of the full row extension to this headline was attempted but did not elaborate within the standing limits. No successful specialized extension is claimed.

### V380 (inversion, D197 escalation 2): exact partial statement

For canonical source QM31 values `chi` and `slot`, with `decode chi ≠ decode slot`, `PV_L2_InversionQ.logup_operand` proves:

```
∃ operand inverse,
  field.QM31.sub (source chi) (source slot) = ok (source operand) ∧
  Canonical operand ∧ decode operand ≠ 0 ∧
  field.QM31.is_zero (source operand) = ok false ∧
  kernels.inverse_q (source operand) = ok (some (source inverse)) ∧
  Canonical inverse
```

`branch_nonzero` concerns the actual extracted zero test. Inversion success is a conclusion, not a hypothesis. `PV_L2_InversionPole.producer` and `consumer` derive the needed inequality from model `NoPole trace lam (decode chi)` for every active copy row and either slot, retaining the explicit correspondence `decode slot = copyRowValues ...`. `logup_all` aggregates any reached-slot list without requiring P_R1 success or accepted attempts. `zero_exact` also characterizes the actual inverse's `none` result.

Source anchors are `crates/aspis-statement/src/logup.rs:199–214` and selected guards in `crates/aspis-r1-cost-probe/src/host_semantic.rs:247–258,273–297`. **The requested whole statement remains OPEN:** native reached-call enumeration and slot correspondence are unproved; generic CodeField, M31, WideExact, circle/fallback, interpolation, quotient-pivot and certificate paths still need caller nonzero arguments on the headline coupling. No reachable valid-spend witness-dependent zero counterexample was established. The successful partial theorem is not evidence that all those paths are safe.

The inspected research ledger already assigns V380 to `TrustedStd.btree_entry_or_insert_with`. This report uses **V380 (inversion)** only for the user-requested D197 obligation. The two must remain distinct pending lead assignment; the shared ledger was not edited.

### F5 and F6: complete extracted references, not complete row closure

`PV_L2_F5SparsePred`, Width, Suffix, Weight, Sum and `PV_L2_F5Mle.erases` cover the full extracted sparse MLE reference, including comparison positions, checked failures and loop limits. Field operations are retained at their extracted call sites; native fixed-latency/operand trace association remains V368. `PV_L2_F5DivPass.pass_erases` covers the full extracted `sampler.qm31_div_pass` reference, including dividend/divisor, remainder, index and stopping prefix. Its eight-step unrolling follows the decreasing index; it is not an increased verification bound. The remaining sampler, gamma, circle and fallback caller trace is unproved.

`PV_L2_F6Checker.erases` covers the whole actual extracted `R1CertCheck.check` for arbitrary public inputs and certificates, including malformed inputs and checked failures. Supporting identity/echelon/permutation/null-vector/lift/entry/product/half/QPrime/BCond references compose through a recorded bind that retains prior events on fail/div. `PV_L2_BoolTrace` records short-circuit conjunction. `PV_L2_RecordCompact.bind_eq` and `PV_L2_RecordRefinement.bind_erases` avoid pathological kernel conversion while preserving the reference's value projection.

These are value erasures for instrumented references. Native branch/address/cost equivalence, allocator/std semantics and certificate generation as a function of coupled challenges remain unproved. Complete extracted checker coverage therefore does not close V364. `proposed/PV_L2_F6CheckerFailure.lean.txt` is explicitly uncompiled and contributes no result.

## Complete row table and premise mapping

All field names below are in `PV_L2_Premises.PV_L2_Premises`. They organize residual obligations; packaging a whole row as a field is not counted as a substantive REDUCED result.

| Ledger row | Field | Status | Proved support; remaining whole-row obligation |
|---|---|---|---|
| V352 entropy draws | `V352` | OPEN | Failure-preserving full L1 carrier; native OS/E1 seed and environment event law still needed. |
| V353 source expander | `V353` | OPEN | Full owned reads/counts, bounds and seed transport; actual ROM scheduling and joint law still needed. |
| V354 mask expander | `V354` | OPEN | Same owned machinery; native mask/refill/rejection history and joint law still needed. |
| V355 simulator coins | `V355` | OPEN | Inherited fixed-coin absorption; real joint prefix law for all coin consumption still needed. |
| V356 sampler/circle | `V356` | OPEN | Full division-pass erasure; gamma/circle/fallback and challenge trace law still needed. |
| V357 sparse/point claims | `V357` | OPEN | Full extracted sparse MLE erasure; native capacity/column addresses/interpolation and prior-FS factoring still needed. |
| V358 QueryScan | `V358` | OPEN | Inherited raw-history lazy/completed transport; native full-history trace association and simulation law still needed. |
| V359 openings | `V359` | OPEN | Native sort/dedup, salts/addresses, sibling sharing, Vec growth and padding cost law still needed. |
| V360 checker phases | `V360` | OPEN | Extracted checking values supported; P_R1/certificate/timer/panic/retry factoring still needed. |
| V361 elimination | `V361` | OPEN | Some extracted checker references; native pivots, zero skips, swaps, inverse branches, rank and allocation trace still needed. |
| V362 descriptors | `V362` | OPEN | Query/lane/layout/relation and coefficient construction trace law still needed. |
| V363 six fills | `V363` | OPEN | All six native fill entry points and supporting selector/arithmetic/source loops still need complete factoring. |
| V364 complete checker | `V364` | OPEN | Whole extracted checker value erasure; native cost/trace association and coupled certificate distribution still needed. |
| V365 BTree/oracle | `V365` | OPEN | Functional laws insufficient; full byte comparison/map/parent/callback cost history still needed. |
| V366 joint raw input | `V366` | OPEN | Conditional SAME-cp full-run extension; native event association and concrete row-field instances still needed. |
| V367 F1 pole kernels | `V367` | OPEN | QM31 partial no-pole branch result; adopted CT kernels and complete two-run caller trace still needed. |
| V368 F2 witness kernels | `V368` | OPEN | Zero/decoder leaves and extracted references; complete native witness caller trace still needed. |
| V369 TLS | `V369` | OPEN | Selected shipped feature and retained observer effects still need artifact association. |
| V380 inversion (D197) | `V380_inversion` | OPEN | Conditional LogUp nonzero result; ALL reached M31/QM31/WideExact inversions outside existing headline bad events still needed. |

Before: 18 inherited whole rows OPEN plus the newly requested inversion obligation. After: the same 19 obligations OPEN, 0 CLOSED, 0 REDUCED. The additional 121 theorem results are support, not 121 eliminated premises.

Endpoint before/after is identical: RustRealRefinement/real RunJoin, E1/E2, prover-proved = prover-shipped, L1/L2/L3, client proof-account route and dependency-closure obligations are retained. Removed: none. Changed endpoint premises: none. Added endpoint premises: none. The new conditional extension separately has 19 explicit row hypotheses. `simE`, observable bytes plus side channels, charged bad events, headline bound and artifact pins are unchanged. There are no edits under `crates/` or `programs/`.

## Validation, receipts and limitations

[Receipt index](INDEX-CONTINUATION.md), [summary](SUMMARY-CONTINUATION.json), [axioms audit](AXIOMS-CONTINUATION.md), [audit manifest](FINAL-AUDIT-MANIFEST.json).

- Lean: 100 attempts, 59 successful. Every final `PV_L2_*.lean` source hash matches a successful compile receipt across the two allocations. J21999 compiled `R1Z/PV_L2_F3SeedPrefix`, exit 0, wall 0:03.87, peak RSS 4,304,812 KiB, swap 0. Its final audit covers 121 distinct new theorem declarations across 59 continuation modules. Only `propext`, `Classical.choice`, `Quot.sound`, or no axioms occur. Failed elaboration prints are not proof evidence. See exact per-theorem output in the audit and raw receipt.
- All host Lean runs used the shared capped launcher with 6G/8G/swap0, TasksMax128 as accepted by lead ruling (b), Lean -M7000. Initial direct execution returned shell126 without launching Lean; `bash run-joint.sh` fixed invocation without changing infrastructure. No barrier refusal consumed a fresh compile. No cap was raised.
- Large null-vector bind conversion reached about 7,170,472 KiB and failed, including J21917. Named component splits and compact bind refinement replaced it; the successful replacement is not an unchanged larger-cap replay. Direct headline extension also hit elaboration time limits and remains unproved. Per-attempt diagnostics document these failures.
- Policy deviation: J21976 was accidentally launched while yielded J21975 was still running, violating the one-scope rule. Both retained the stated caps; J21976 lasted 3.02 seconds. Both receipts record the overlap. No aggregate-limit bypass or cap increase was made.
- Kani: 20 charged runs, 17 passes; z01 CLI rejection, z02 source-assembly rejection, z07 proof-side memcmp unwinding failure. The z09 replacement uses pointwise limb comparisons without raising the failed bound. None of the predecessor's timed-out harnesses was rerun unchanged. All use 6G/8G/swap0 and TasksMax64.
- Kani source binding: 13 exact source bodies from rebase candidate `351c5c7f6b6ac0110459192ef1c55e25a6c80c67`, explicitly different from this branch's unchanged crates. `zero-source-binding.json` pins each body. No arithmetic or inversion stubs. Successful checks cover zero predicates, canonical limb/byte decode, roundtrips, selected invalid limbs, arbitrary chosen nonzero limb and wrong lengths 0–33 excluding32. These leaf/representation checks do not establish caller reachability or machine timing.
- Generator manifest checks passed for the eight simple checker modules, ten outer modules and eight half-check components. The continuation summarizer verifies all source/receipt hashes, all20 Kani snapshots and standard axioms without compiling.
- Each receipt records target, exit, wall, RSS, swap, source baseline revision and axioms (Kani: N/A). Exact submitted source hashes identify proof edits beyond that baseline. Direct object hashes were collected after runs, not from a frozen transitive replay. Not every failed intermediate source snapshot survives; their hashes and diagnostics do. No full frozen release manifest replay was run: the native source/coupling cone remains incomplete. No runtime/ELF suite was warranted by these proof-only changes.

## Stop and next deliverable

Stopped at exhaustion of both fresh allocations, not at privacy completion or a checked witness attack. No further compile was launched beyond J21999.

Next deliverable: identify the native E1 64-byte seed event producer and each source/mask invocation with the rich full-L1 runner, associating actual ordered ROM entries on rejected and stopping attempts. Instantiate that association on the headline's existing coupling and actual realBad union, then prove whole-record source-to-unchanged-simE absorption. Separately enumerate every reached inversion call and discharge its operand nonzero condition from that same union, including M31/WideExact and certificate paths. F5/F6 then need complete native cost association and challenge/certificate factoring, rather than additional value-erasure helpers alone.
