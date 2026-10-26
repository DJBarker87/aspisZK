# L2 simulation handoff — 2026-10-26

Branch `codex/pv-l2-sim-20261026`, base research
`a0c5e1f66a9d16f76a22bd77fb0bc499a64a9978`. Design was committed first as
`2e103c4017`, before proof code. No Lean/Rust proof code was added and no
shipped source changed. This is a design/source-interface review and blocked
build handoff, **not** an L2 privacy proof.

## Established by review

`design/PV-L2-SIM-20261026.md` defines the intended joint observable and
the theorem target, retains the headline's actual simulator and bad-event
envelope, and inventories every F3/F5/F6 row of the requested v2 table.
It distinguishes deterministic trace control from a proved law for its inputs.

The current proof interfaces do not supply a complete joint trace join:

- `PrivacyR1HeadlineDeployedReal.RustRealRefinement` joins the existing
  view/observer decision and named failure/query interfaces, not new L2 events.
- `QueryScanRealLazyBound.real_vector_toRP` preserves all normalized honest
  answer coordinates off `lazyBad`; a deterministic observation of that vector
  can be transported there. This alone does not cross the later witness-mask
  absorption step to `simE`.
- `ProverCommitQuotientCoupling.completed_view/middle_completion` preserve
  the published view/retry test after completing the middle tape. They do
  not conclude preservation of expander refill/rejection histories.
- `SideChannelEntropy` preserves draw-count/status histories for successful
  seed relabelings, while the requested L2 observer also sees byte-comparison
  positions. The L1 report explicitly leaves composition with the masked
  transcript open. It is not a completed layer that can simply be assumed.
- `ProverCommitReencode16.recover/reindex` and `PhaseWireLog2Bin.opens`
  specify logical disclosure/order. They do not specify BTree/sort/Vec costs.

No checked witness-dependent valid-spend counterexample was found or asserted.
The inherited leaf counterexamples refute proof inferences, not this protocol.

## Row status

Locations are the assigned CT-KERNELS v2 anchors, with abbreviations defined
in the design note. “Open” applies to the complete requested row. A dash in
the theorem column means no new theorem was checked; inherited local results
in `evidence/l2-leaf-20261025/REPORT.md` are not promoted to row closure.
`B0` below is `launch-receipt.json` plus `launcher-J20100.log`, documenting
the common build block, not a per-row proof receipt.

| Row (file:line) | Status | New theorem | Receipt / next missing evidence |
|---|---|---|---|
| F5 probe/sampler.rs:8,21,45,102,111,121; probe/r1_wire.rs:194,209,256; probe/transcript.rs:23,31 | open | — | B0; native division/gamma trace and raw-prefix joint transport |
| F5 core/circle.rs:34,55; core/r0_transcript.rs:177 | open | — | B0; singular/subfield/inverse/fallback source trace |
| F5 statement/constraints_v4.rs:601,654,782; probe/host_semantic.rs:31,204 | open | — | B0; sparse-point control refinement and history law |
| F5 core/r0_transcript.rs:202,216,305; probe/transcript.rs:35 | open | — | B0; full duplicate/extra-block/exhaustion observation on actual parser |
| F3 prover/state_only_entropy.rs:202 | open | — | B0; E1 byte-position observation jointly with L1/view |
| F3 prover/state_only_entropy.rs:760,780,794,804 | open | — | B0; actual expander/refill/rejection-history join |
| F3 prover/state_only_hiding.rs:330,350,361,371 | open | — | B0; private-mask expander joint join |
| F3/F6 probe/sim.rs:79,80,84 | open | — | B0; simulator/real nonzero-loop joint law |
| F5/F6 probe/prover.rs:253,266; probe/host_commitment.rs:220,229,242; probe/multiproof.rs:54,198,248,251 | open | — | B0; native addresses/sort/dedup/sharing/Vec trace |
| F6 probe/prover.rs:307,354; z4/z9e.rs:50,90,184,196 | open | — | B0; hidden-attempt challenge factoring and phase/error traces |
| F6 z4/z9c.rs:107,135,290,332; z4/z9d.rs:17,41,74,90,113 | open | — | B0; full elimination/pivot/certificate trace |
| F6 z4/z9.rs:567,989,1010,1016; z4/z9b.rs:78,107; z4/probe.rs:2207,2214,2256 | open | — | B0; concrete descriptor/challenge factoring |
| F6 c3/build/src/lib.rs:108,317,358,539,820,918 | open | — | B0; six actual fill-loop source joins |
| F6 c3/check/src/lib.rs:27,40,56,81,96,138,149,160,171,182,193,204,215,227,243,255,270,275,370,384,407 | open | — | B0; actual checker/failure-prefix source joins |
| F6 probe/sim.rs:99,114,133,358,368,396,439 | open | — | B0; actual collection comparison/callback history semantics |

## Infrastructure stop and budget

The existing launcher was inspected and invoked as:

```
ssh dombarker@100.108.41.90 'sh /home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh 20100 R1Z/PV_L2_F5 J 7000 8'
```

It exited **64**, `attempt 20100 outside 5000-9999`, before source lookup or
any compiler/scope. `PV_L2_F5` is a planned target, not a submitted module.
Its source SHA/dependency fingerprint and `#print axioms` are therefore N/A.
No host wall/RSS/swap measurements exist; null fields in the receipt are
intentional. Local SSH round-trip time is separately labelled.

The observed launcher additionally specifies `TasksMax=128`; this job requires
64. The common instructions permit changing **only** the accepted ID range.
That permission cannot repair the task-cap mismatch. The binding
`local-lean.txt` rule 5 says: “Do NOT build or repair build/launcher/monitoring
infrastructure. If the launcher or host misbehaves, stop and report the exact
error in one paragraph; the lead fixes infrastructure. Proof work only.”
Accordingly no launcher change, alternative host runner, uncapped compile,
cold local dependency build, or repetition of this rejected launch was made.
This is not a reservation-barrier refusal, so the barrier retry rule does not
apply. The launcher snapshot and SHA-256 are committed as evidence.

Budget consumed: **0/100 Lean compiler attempts, 0/20 Kani runs**; one rejected
launcher preflight reserved J20100. No axioms audit or final manifest replay
ran, and no formal theorem or source check is claimed from the diagnostic.
Kani work was not started because the mandated order stops at F5 proof/build
preflight, and the instructions require an infrastructure stop.

## Premise/ledger accounting

The privacy ledger file is absent on the checked research revision. No ledger
row is removed. Before/after are identical: the deployed `RustRealRefinement`
and D159/D166 joint L1/L2 deployment conditions are retained in full. No new
agreement hypothesis, bad event, runtime trust item, simulator or observer is
introduced. The 100-bit deployed privacy target is **not yet established**.

Next concrete deliverable: lead supplies a compliant existing Env-J launcher
for J20100–20399 with TasksMax 64; then implement/compile `PV_L2_F5` against
the actual QueryScan real-vector/parser definitions, followed by the concrete
joint transport across tape absorption. That first bridge must be labelled
real-to-lazy until the simulator leg is discharged.

## Resumed execution, 2026-10-26

The lead's 09:50 rulings supersede the infrastructure stop above: J20000–29999
and TasksMax=128 for the existing Lean launcher are accepted. The launcher
was not edited. Baseline is 5048eb9408 on the same assigned branch.

Stage F5: `PV_L2_F5.history_prefix` (J20104) checks prefix preservation on the
actual `PhaseSamplerParserBin.parsedWords/scanned`, `PhaseQueryScanBin.stop`
and `Q22WordScan.finish`. `history` includes raw block prefix, per-block
state, ordered comparison operands/results, duplicate decisions and guards,
first stop and failure. This is a Lean parser observation; native contains,
Vec allocation and machine trace correspondence remain open.

`PV_L2_F5Transport.real_to_lazy` (J20106) uses the actual
`QueryScanRealLazyBound.real_vector_toRP` with the SAME `lazyBad`, `RAddrIn`
and `RCausal`. `lazy_to_middle` identifies it on actual `gM` coins.
`completion_joint` preserves this history jointly with the whole view across
`gMQ` quotient tape completion. This is real-to-lazy plus quotient completion,
NOT yet witness absorption or `simE`. No new agreement premise is introduced.

Receipts: J20101–J20106 subdirectories (four initial local theorem errors,
then passing F5 J20104 and transport J20106). Each records source SHA,
direct cached-object fingerprint, exit/wall/RSS/swap and full axiom output.
Failed elaborations print sorryAx and are explicitly excluded from proofs.
Passing top theorems use only propext, Classical.choice, Quot.sound.
No shipped file changed, no existing proved module overwritten.
Endpoint premises removed: NONE at this stage. Deployment L1/L2, source
refinement, E1/E2 and the simulator leg remain retained in full.

Stage F5 absorption: `PV_L2_F5Absorption.fixed_coins_joint` (J20108)
uses the actual `SimulatorR1.hvzk_R1S` and unchanged `RefPayload.simE`.
For a fixed full attempt-coin vector and selected P_R1/VR1-valid challenge,
every test of (all raw QueryScan histories, selected honest view) has the
same mean as (the same histories, simE view). PackField, PublicBase,
BuilderSoundOn, P_R1, VR1 and public-instance equality are explicit inherited
hypotheses. This supplies a fixed-coins absorption leg, not the native
retry/L1/ROM-history joint endpoint. No trace-agreement assumption was added.

`PV_L2_F3Words` (J20110) constructs a symbolic equivalence on all 31-bit
candidates, fixes the unique rejecting cell P, and proves complete bounded
scalar rejection-control preservation under any canonical-value permutation.
It is a candidate-word lemma, not yet a Rust-word/ROM/E1/L1 source join.

### Stage F3 and F6 focused evidence

J20113 `PV_L2_F3Schedule`: scalar/tower values move by a canonical-value
permutation; full cap-16 rejection histories, cursors, refill offsets and
four-limb partial-failure prefixes stay. This is candidate-level semantics.
J20116 `PV_L2_F3Adaptive`: a genuine finite-stream equivalence advances the
logical permutation index only at accepted scalars, preserves every accept
bit and the exact uniform input law. J20129 `PV_L2_F3WordCarrier` transports
it to the ACTUAL `CommitReadsR1.Word`/`ProverCommitWordCarrier.accepted`:
retained high bit, identical rejection Boolean, canonical output permutation.
The whole block-byte decoder/owned-caller/witness-translation join is not yet
proved by these separate facts.

J20123 `PV_L2_F3Recorded.qm31_erases` records the ACTUAL extracted owned
`next`/cap-16 scalar and four-limb caller. Erasure is proved by induction,
including hash failure/divergence and scalar partial failure; no scalar stub.
Read records contain raw proof inputs, not an assertion that all answer
values are public side-channel leakage. It is not a native-machine trace.

J20118 `PV_L2_F3SeedObstruction.lifted_position_changes` is a CHECKED
COUNTEREXAMPLE TO AN INFERENCE, not to valid-spend witness privacy. Swapping
successful seed pairs with nonzero bytes in positions 0 versus 1 preserves
`SideChannelEntropy.count_history_preserved` for every public nonce and
byte-blind fault schedule, but changes `firstNonzero`. This forbids using
arbitrary successful-seed relabeling for the stronger observer. No row is
marked witness-dependent on this evidence; the rows remain open.

J20126 `PV_L2_F5Machine`: recursive instrumented parser erases to Q22 scan,
its history equals the F5 observation, and the existing source-shaped
`Query31ExplicitListLoop.scanListLoop_q22` consumes that recorded result.
The array IntoIter/std cost boundaries of Query31 remain explicit.

J20120 `PV_L2_F6Openings`: the actual `PhaseWireLog2Bin.opens` factors
through queries, with complete `PhaseSamplerParserBin` prefix transport.
J20124 `PV_L2_F6Sharing`: source-linked binary group/cursor structural
record and symbolic singleton sibling count; no native std cost claim.

Kani budget: 20/20 used, 11 successes, eight 50-second timeouts, one
proof-side memcmp unwind failure (k05). Exact source items from current
QueryScan/sampler/multiproof bodies are pinned by tools/.../source-binding.json;
proof harnesses are cfg(kani)-only and contain NO stubs. Standalone Kani
0.67 with bundled sysroot, -j4, one 6G/8G/swap0/TasksMax64 scope at a time.
This is bounded symbolic checking, not an unoptimized arithmetic gate.
All raw logs/times/receipts are k01–k20. Timeout GNU-time wrapper peaks
can undercount descendants; actual peaks are null rather than invented.
No timed-out target was rerun unchanged or at a raised cap. Larger scan/count
scopes moved to the source-shaped Lean references at their stated scope.
Reservation preflight before k18 saw a vanished cgroup; it was retried after
30 seconds once and succeeded. No reservation barrier was bypassed.

### Source-count and extracted-checker stage (supersedes earlier open subgoals)

J20188 proves `PV_L2_F3Absorption.source_count_absorption`: actual owned
quotient plus both scalar draw-count arrays, with common None failure,
transports through uniform completion and `hvzk_R1S` to unchanged simE.
J20190/J20191 connect these counts to the concrete source-shaped collector,
actual domains, empty cache and fixed budgets, then erase to the actual
owned decoder. J20193 specializes to the endpoint field/honest builder,
discharging local builder/public premises using existing admitted proofs.
J20194 retains the entire ideal E1 entropy return/state jointly. This is
not full L1 Run composition, native trace equality or ROM-history transport.

J20141/20153/20160/20186/20196 prove failure-preserving recorded dot,
gathered-dot, pivot, image and product-row loops erase to actual extracted
checker functions. They do not yet prove certificates factor through coupled
challenges or native std/allocator traces. No complete row closes.
All successful printed top theorems use only standard axioms. A full
manifest is not authorized by the incomplete source/coupling cone.
