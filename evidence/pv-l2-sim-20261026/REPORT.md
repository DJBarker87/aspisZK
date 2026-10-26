# L2 joint simulation execution report — 2026-10-26

Branch `codex/pv-l2-sim-20261026`; resumed baseline `5048eb9408`.
Proof only. **Budget exhausted: 100/100 Lean compiler attempts, 20/20 Kani
runs. No complete F3/F5/F6 deployment row is closed. The privacy target is
not established.** No shipped source, simulator, observer, bad-event envelope,
release pin or existing soundness file changed. Work is committed, not pushed.

This report supersedes the inherited blocked handoff. The lead's 09:50
rulings accept IDs 20000–29999 and the shared launcher's TasksMax=128.
No launcher modification was made by this worker. The inherited J20100
range refusal consumed zero compiler attempts. The design remains
[PV-L2-SIM-20261026.md](../../design/PV-L2-SIM-20261026.md).

## What is proved

All module names below have prefix `R1Z.PV_L2_`. Actual parser inputs, not
accepted-query sets alone, are used. `F5.history_prefix` records the raw read
prefix, per-block state, ordered contains comparisons, duplicate/accept
branches, first stop and failure using `PhaseSamplerParserBin.parsedWords`
and `scanned`, `PhaseQueryScanBin.stop`, and Q22 finish. `F5Machine.execute`
is a recursive instrumented implementation: its value erases to the actual
Q22 scan, its events equal that observation, and `source_loop_record` joins
the existing source-shaped explicit-list loop. Native array iteration, std
and allocator traces are still separate obligations.

`F5Transport.real_to_lazy` is **real-to-lazy**, off the same `lazyBad`, with
the existing `RAddrIn`/`RCausal`. `lazy_to_middle` and `completion_joint`
carry the raw parser history jointly with the complete view through actual
middle-tape completion. `F5Absorption.fixed_coins_joint` then carries all
attempt parser histories through the existing `hvzk_R1S` to unchanged
`simE`, for fixed complete coins and a selected P_R1/VR1-valid challenge.
`Headline` specializes to the exact W, Pr, owned decoder, eight-attempt
reencoded source and honest builder of `privacy_headline_deployed`.
This supplies a simulator leg at this stated model scope; it does not turn
the complete real/L1/L2/ROM retry experiment into a proved joint theorem.

F3 now has actual 32-bit word transport preserving the high bit and rejecting
cell, adaptive finite-stream equivalences, bounded cap-16 scalar/four-limb
records, and concrete source-shaped `next`/collector erasures. Counted
conditional fibres are proved symbolically, first for words, then actual
oracle blocks, both streams and the owned quotient tape. These are exact
joint laws, not an inference from marginal uniformity. `F3SourceArrays`,
`F3SourceBudget` and `F3SourceJoint` connect both complete scalar draw-count
arrays to actual empty-cache source collectors, actual caller domains and
existing fixed capacity/budget proofs, and erase to the endpoint's owned
decoder. `F3CompletionLaw` proves the independent padding/completion law.
`F3Absorption.source_count_absorption` transports the owned quotient plus
both count arrays through completion and witness absorption to unchanged
simE. `HeadlineF3.absorption_actual` specializes to the endpoint's field,
honest builder and public statement, with P_R1/VR1 guards retained.

`F3EntropyPrefix` fixes the entire raw E1 seed tape and actual public-nonce
entropy return/state, so successful seed byte positions are unchanged.
`F3EntropyJoin.entropy_count_absorption` retains that full entropy result
jointly with count/view absorption in the ideal independent coordinates.
This is **not** composition with `SideChannelL1AttemptRecord.Run`: all
rejected attempts, failed scalar prefixes, actual ROM requests/history,
allocation/drop/environment state and their native event producers remain
unjoined. `None` in the count law preserves decoder failure as the same
outcome; it does not retain its detailed partial observation.

F6 proves logical opening dependence on actual queries and source-linked
binary sharing/cursor structure. Failure-preserving recorded dot, gathered
dot, pivot, image, product-row and complete product loops erase to the
actual extracted checker functions. Checked arithmetic/index errors and
nested fail/div prefixes are retained; multiplication/remainder operands
are explicitly recorded. These results do not establish that generated
certificates/matrices factor through coupled challenges, nor native costs.
No abstract callback supplies the desired arithmetic result.

## Row table

Anchors are the assigned CT-KERNELS v2 locations; probe/prover/core/statement
abbreviations and z4/c3 paths are defined in the design. **OPEN** means the
whole requested row. Theorems below are partial evidence only. J and k
references link through [the full receipt index](INDEX.md).

| File:line → row | Status | Checked theorem / source result | Receipt → remaining join |
|---|---|---|---|
| probe/sampler.rs:8,21,45,102,111,121; r1_wire.rs:194,209,256; transcript.rs:23,31 → F5 | OPEN | Bounded exact-body gamma/zero-divisor checks | k08,k18–20; division k09 timeout → full division/circle call schedule and raw-prefix joint law |
| core/circle.rs:34,55; r0_transcript.rs:177 → F5 | OPEN | No new complete source theorem | no row receipt → singular/subfield/inverse/fallback trace |
| statement/constraints_v4.rs:601,654,782; probe/host_semantic.rs:31,204 → F5 | OPEN | No new complete source theorem | no row receipt → point/control refinement on every reached attempt |
| core/r0_transcript.rs:202,216,305; probe/transcript.rs:35 → F5 | OPEN; actual model/parser transport proved | `F5.history_prefix`, `F5Machine.source_loop_record`, `Headline.real_to_lazy_actual`, `Headline.absorption_actual` | J20104,20106,20108,20126,20134; k01–03,06–07 → native iteration/std costs and whole retry/L1/ROM join |
| prover/state_only_entropy.rs:202 → F3 | OPEN; ideal E1 prefix retained | `F3EntropyPrefix.actual_entropy_preserved`, `F3EntropyJoin.entropy_count_absorption` | J20132,20194; J20118 obstruction → full L1 Run/retry/ROM composition |
| prover/state_only_entropy.rs:760,780,794,804 → F3 | OPEN; source counts/quotient absorption proved | `F3Recorded.qm31_erases`, `F3SourceBudget.entropy`, `F3SourceJoint.source_owned`, `HeadlineF3.absorption_actual` | J20123,20171,20181,20190–91,20193 → native refill/request/rejected-prefix and L1/ROM joint record |
| prover/state_only_hiding.rs:330,350,361,371 → F3 | OPEN; source counts/quotient absorption proved | `F3SourceBudget.masking`, `F3Tape.owned_joint_law`, `F3Absorption.source_count_absorption` | J20165,20188,20190 → same native/full-history join, no replacement independent mask |
| probe/sim.rs:79,80,84 → F3/F6 | OPEN | No cap/unbounded-loop equivalence claimed | no row receipt → actual simulator nonzero loop/order/exhaustion joint law |
| probe/prover.rs:253,266; host_commitment.rs:220,229,242; multiproof.rs:54,198,248,251 → F5/F6 | OPEN; logical/structural subset proved | `F6Openings.parser_prefix_opens`, `F6Sharing.cursor_joint`, `singleton_count` | J20120,20124; k10,k15 pass, k11–14,16–17 timeout → native sort/dedup/Vec/std and payload validation |
| probe/prover.rs:307,354; z4/z9e.rs:50,90,184,196 → F6 | OPEN | No complete phase-source theorem | no row receipt → challenge/emit/convert/check/error/panic phase factoring |
| z4/z9c.rs:107,135,290,332; z9d.rs:17,41,74,90,113 → F6 | OPEN | No new complete elimination theorem | no row receipt → actual challenge-to-matrix/rank/pivot trace |
| z4/z9.rs:567,989,1010,1016; z9b.rs:78,107; probe.rs:2207,2214,2256 → F6 | OPEN | No new descriptor theorem | no row receipt → concrete descriptor and reached-challenge refinement |
| c3/build/src/lib.rs:108,317,358,539,820,918 → F6 | OPEN | No six-fill trace theorem | no row receipt → concrete fill loops and descriptor/challenge factoring |
| c3/check/src/lib.rs:27,40,56,81,96,138,149,160,171,182,193,204,215,227,243,255,270,275,370,384,407 → F6 | OPEN; extracted subset recorded | `F6Dot.dot_erases`, `F6KDot.kdot_erases`, `F6Image.image_erases`, `F6Pivot.piv_erases`, `F6Product.product_erases` | J20141,20153,20160,20186,20196,20198–99 → remaining checkers, generated certificate/challenge factorization and native refinement |
| probe/sim.rs:99,114,133,358,368,396,439 → F6 | OPEN | No native collection trace law | no row receipt → BTree paths/key bytes, callbacks, sharing and joint programmed history |

## Counterexample and owner decision boundary

`F3SeedObstruction.lifted_position_changes` (J20118) is a checked
counterexample **to a proof inference**: successful raw seed pairs with their
nonzero byte at positions 0 versus 1 can be swapped while the old
`SideChannelEntropy.count_history_preserved` still holds for all public
nonces and byte-blind fault schedules. The first-nonzero comparison position
changes. Therefore arbitrary successful-seed permutation cannot justify the
stronger observer. The replacement ideal construction fixes the raw E1 tape.
This is not a valid-spend, same-public-statement witness attack. No genuinely
witness-dependent row was established, so no row is marked closed or STOP
on that basis. The obstruction is recorded for owner review here and in
J20118; no messages were sent to third parties.

## Premises before and after

| Item | Before | After / effect |
|---|---|---|
| Endpoint `PrivacyR1HeadlineDeployedReal.RustRealRefinement` / `ProverCommitFuelJoin22.RunJoin` | Required, with existing view/failure/query interfaces | Retained identically; no arbitrary new L2 trace interface inferred |
| E1/E2; prover proved = shipped; L1/L2/L3; client proof-account route; dependency-closure replay | Open deployment conditions | All retained; **zero endpoint premises removed** |
| Local F5 `RAddrIn`, `RCausal` | Explicit in generic real-to-lazy theorem | Discharged in `Headline.real_to_lazy_actual` by existing coverage/address/causality proofs; no new runtime assumption |
| Local `PublicBase`, `BuilderSoundOn` | Explicit in generic absorption | Discharged in `Headline.absorption_actual` and `HeadlineF3.absorption_actual` by existing admitted builder proofs; no endpoint premise removed |
| `PackField`, public-instance equality, P_R1, VR1 | Existing model absorption guards | Retained, with actual packing theorem at headline specialization; rejected-P attempt traces not silently covered |
| Capacity/word budget, equal conditional fibres | Initially explicit generic lemmas | Capacity/budgets discharged for actual domains in `F3SourceBudget`; conditional fibres proved for actual owned decoder; no trace-equality assumption added |
| Source failure | Actual decoder can return None | Same None in both laws; failed-prefix trace join explicitly retained, no new allowed error |
| Simulator, observer, bad-event bound | Actual simE; bytes + oracle history + L1/L2/L3; existing bound | Identical. No new bad event, observer restriction, simulator replacement, bound charge or runtime trust item |

The headline bound remains the design's existing model error, parser/fresh
collision, seed-hit and fuel terms. These proofs do not charge missing trace
agreement to one of those events. No ledger row was invented where the
privacy ledger is absent in this branch.

## Validation and measured evidence

- **100 Lean compiles**, J20101–J20200: 45 successes, 55 failed elaborations;
  every final module hash matches a successful compile. Each changed generic
  target was compiled before its consuming bridge. No unchanged failed compile
  was rerun at a higher cap. No broad numeral/recurrence evaluation or cap
  override was introduced. Lean peak observed across runs: 4,268,660 KiB;
  all GNU-time swaps zero. Full resources, source revisions/hashes and direct
  object hashes: [INDEX.md](INDEX.md) and per-attempt JSON/raw logs.
- **Final focused audit**, J20200, `R1Z/PV_L2_Audit`: exit 0, wall 0:02.01,
  peak 4,265,580 KiB, swaps 0, source baseline `4d0b6c1713` plus exact submitted
  source hash in receipt. All **140** printed declarations use only subsets
  of `propext`, `Classical.choice`, `Quot.sound`, or no axioms. The result for
  **each declaration** is [AXIOMS.md](AXIOMS.md); raw output is J20200/out.log.
  Failed elaborations' `sorryAx` prints are excluded from proof results.
- **20 Kani runs**, 11 pass, eight 50-second timeouts, one proof-side memcmp
  unwind failure (k05). Full scoped outcomes are in INDEX.md. Exact 13 Rust
  items are bound by `tools/pv-l2-sim-20261026/source-binding.json` and the
  generator reproduces the checked file byte-for-byte. Proof modules are
  `cfg(kani)` only, bounded and stub-free. These checks have their harness
  scope; they are not whole-row or full native-trace equivalence results.
  Larger unsuccessful scan/count scopes moved to source-shaped Lean references;
  the unproved native equivalence is retained, not asserted as P6 completion.
- Shared Lean launcher: `-M7000`, MemoryHigh=6G, MemoryMax=8G, swap=0,
  TasksMax=128 (accepted lead ruling). Kani: standalone 0.67.0 bundled sysroot,
  -j4, own 6G/8G/swap0/TasksMax64 scopes. One capped scope at a time; pinned
  workspace/cache reused. No dense arithmetic gate or unoptimized Rust gate.
  Before k18 a vanished-cgroup reservation error was retried once after 30s;
  see reservation-k18-retry.json. No barrier was bypassed.
- The J20181 unchanged-source preflight refusal (exit 67) occurred because
  an intended edit did not match. It launched no compiler; the source was
  corrected before successful J20181. Separate JSON records the refusal.
  J20100 is the inherited pre-ruling range refusal, also charged zero.
- Read-only regeneration/checks: exact Rust binding reproduction, prohibited
  proof-token scan, final module/source receipt hash checks, `git diff --check`,
  and no differences under crates/ or programs/ against baseline. No full
  frozen deployment manifest was replayed: the source/coupling cone remains
  incomplete. This is a focused proof result, not a formal release result.
- Exact source SHA and raw diagnostics survive every failed run, but not
  every intermediate failed source file. Collected dependency hashes describe
  direct cached objects after the run, not a complete frozen transitive
  closure. These limits are not hidden by the baseline revision field.
- A local small-file write briefly failed with ENOSPC; a later space check
  showed 4 GiB available and the write succeeded. No wallet/key cleanup or
  deletion of other work was performed.

Reproduce receipt/audit consistency without a compiler:
`python3 tools/pv-l2-sim-20261026/summarize.py`.
Proof commits through the final audit are listed in [HISTORY.txt](HISTORY.txt);
the final report-only commit is additionally identified in the final response.

## Stop and next concrete deliverable

Stop reason: both authorized budgets exhausted. Neither a launcher issue nor
Kani timeout is being used as the stop. No release/privacy completion claimed.

Next deliverable: a concrete failure-preserving E1/expander event producer
joined to `SideChannelL1AttemptRecord.Run` on **every reached/rejected attempt**,
with raw refill/address/rejection prefixes and actual ROM programming/history.
Prove its success projection equals `F3SourceJoint.sourceObserved`; join its
failure prefix without collapsing it to None; transport that complete record
through the same witness coupling with unchanged simE and existing bad events.
In parallel proof order, finish source-controlled F5 sampler/circle/sparse
factoring and the remaining F6 checker/build/collection traces. No native std
trace may be inferred solely from functional equality. New budget is needed
for those focused gates and only then a complete frozen dependency replay.
