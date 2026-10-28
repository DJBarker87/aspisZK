# L2D handoff — target remains unestablished

Branch `codex/pv-l2d-20261028`, exact worktree
`/Users/dominic/ZK/.worktrees/pv-l2d`, base
`1e826627aa39fe02569bf840efb894eaa287efcf`. Authorized RunJoin merge
`7d733ebb76` was conflict-free. No changes under `crates/` or `programs/`,
including that merge. No keys/accounts created or destroyed, no transactions,
no push. Host workspace:
`/home/dombarker/project-offloads/codex-pv-l2d-20261028/`.

**Stop: 100/100 Lean compiler attempts exhausted. Kani: 0/6. All ten whole rows
remain OPEN. No endpoint premise removed. No checked honest leak found.**

## Before/after premise accounting

For each V353, V355, V356, V358, V359, V361, V362, V363, V364, V365, before and
after is the SAME `PV_L2_Premises.PV_L2_Premises.Vxxx` field:
`∀ s, ¬(∃ i, bad old queries i (join.cp.toM s)) →
 realRows (join.cp.toR s) .vxxx = modelRows (join.cp.toM s).1.1 .vxxx`.
No replacement coupling, additional bad event, extra T item, premise removal,
or weaker observer/simulator. CanonicalHonest31 was merged, but its successful
preparation result has not been associated to the complete native observers.
`scope-status.json`, `rows-before.json`, `REMAINING-ROWS.md` give per-row status.

## Proved, measured, inspected

| Row | Accepted helper result / evidence class | Whole-row non-vacuity |
|---|---|---|
| V353 | Complete scalar and four-limb outcomes/state/event prefixes; public-clock trace reconstruction; joint ideal rejection/value mass and translation. Partial **structural (K-1 substitute)** inventory, four-byte slice equality, finite native expander validation. | Initial/zero-word and four directed failure controls; successful canonical preparation association missing. |
| V355 | Complete finite prefixes and continuation for the **uncapped** nonzero loop; counter/state law and outer trace reconstruction; one-cycle key uniqueness and repetition after2^64. Finite native coin validation. | Successful/nonterminating model controls and finite native rejection cases; complete fresh-seed/earlier-history association missing. |
| V356 | Exact reverse-division quotient/remainder identity, bounds, casts and written quotient-list invariants. | Arithmetic input domain only; all sampler/circle/fallback paths not established. |
| V358 | Scanner complete per-block results/history, distinctness/index bounds, eager-driver selected advance/exhaustion and explicit native guard orders. Finite complete-result native comparison. | Boundary, duplicate and exhaustion controls; no full canonical-honest joint observer binding. |
| V359 | Complete zero-tail/checker outcome, field embedding upper-zero lemmas, symbolic ordered Merkle plans, occupancy/node caps, safe addresses, publication insertion traces and fixed padding bounds. Finite native checks. | Model/native controls, not whole producer/canonical-preparation support. |
| V361–V365 | Pinned source/control inventory and deployed-feature graph. | Not proved; no native or row theorem claimed. |

Theorems are in `docs/research/v8-r0-zk-20261009/lean/PV_L2D_*.lean`.
The final two combined audits print every helper theorem's axioms.
`V353-WORKING.md`, `V355-WORKING.md`, `V359-WORKING.md` and
`REMAINING-ROWS.md` distinguish each accepted subsite result from retained native,
full-result, ambient-state, simulation and same-cp obligations.

Native finite checks, with their source freezes, full state/results and logs:

* zero-tail:29,216 comparisons; first rustc-path failure retained; changed absolute
  path succeeds. Compiler version was not captured, so no deployed lowering credit.
* Merkle:75,535 binary inputs, three eight-way controls, five invalid inputs.
* publication:141,312 range/flag cases; equal-set/different-control witness.
* expander-v3:17,560 method checks, four limb-failure controls,64 actual SHA seed
  cases; matched false control exits101. Rust1.94.1 release, zeroize1.9.0 deployed
  features and sha2 .10.9, dependency archive/source verification. Earlier failed
  checksum preflight and zeroize1.8.1 configuration retained without deployed credit.
* coins-v1:12,736 finite runs including64 actual SHA cases, synthetic zero prefixes
  and u64 wrap; matched false control exits101. Rust1.94.1 release, sha2 .10.9.
* query-native-v2:20,045 complete-result checks, all43 stop positions22..64,
  matched draw24 false control exits101. Missing block_rank closure in v1 failed
  compilation and is retained; v2 includes the exact decoder.

These finite checks are not universal native laws. Synthetic hash families are
separate from actual SHA cases and do not prove deployed entropy support. No
copy-, function-pointer-, Option<fn>- or chained-field Kani result is claimed.
`metadata-errata.json` corrects copied descriptive strings in the coin receipt
without changing its actual command, source, binary or measurement.

## Validation and provenance

`FINAL-VALIDATION.json`:100 compiler launches,65 focused attempts (27 failed,
subsequently fixed), ONE final32-target focused replay plus three reserved audits
51597–51599. All35 final targets exit0. Peak RSS3,820,312KiB, total swaps0.
Accepted axioms are only propext, Classical.choice, Quot.sound (or none).
Individual `receipt-515xx.json` files retain exact target, source revision/blob/
SHA, exit, wall time, peak RSS, swaps and printed axioms; failed records are not
credited. Native receipts use N/A for Lean axioms. No repeated full regression.

Every heavy process used an admitted capped scope:6G high/8G max/swap0, tasks64,
Lean-M7000. No local Lean compilation. Final preflight rechecked all5,673 h4
external object hashes and the five private project dependencies before the
single coherent private replay. No Stream A project objects or XR definitions
were loaded. The two SHA-frozen ProducerRelease47 modules and three inherited
PV_L2B modules were built privately. Final object/companion hashes are in
`final-private-object-manifest.json`; final source order and hashes in
`final-focused-manifest.json`. Sources/caches retained for handoff.

Ruling(x) check: resolved client features are in `deployed-client-features.json`.
C3 selects native-kernels/native-workers; fallback-only extraction is insufficient
for deployed credit. Effective C3 overflow flags still need actual build receipt
association. The source-only argument that both sides call p_r1_check is not a
proof of matching global transport, panic hook, worker or timing outcomes.

N3 overlap: V359 prefix reachability shares pv-l2c/D371; that audit was not
repeated. `compact_values` checks N8 high16-byte-zero, not canonical limbs.
No N3 closure or new honest leak is asserted here. D188-sensitive mutable
iterator writeback in sampler remains explicit; no affected emission was
credited as native without a fidelity check.

Next concrete deliverable: bind V358's complete eager digest/advance suffix,
failed-wrapper state and source branch/index observer to the actual
CanonicalHonest31 RunJoin on its existing cp, then use the full decoded candidate
history for simE. An accepted query list alone demonstrably loses trace history.
The other native/endpoint residuals remain listed per row; none is silently
assigned to trust. The lead retains target-status authority.
