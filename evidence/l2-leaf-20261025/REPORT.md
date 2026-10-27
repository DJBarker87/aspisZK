# L2 leaf trace work — 2026-10-25

Target: D166 simulatable source traces for the unchanged leaf kernels of D187.
Baseline: 970912bfe7ad33e9b53eb7d65a4c47ae129b3696, branch
codex/cx-l2-leaf-20261025. No adoption or deployed privacy claim.

## Stage 1: source and contract

The observation includes branch outcomes (including short-circuit comparisons),
array addresses, loop visits, allocation requests, variable-latency arithmetic
calls, and collection operations. Allocation failures, allocator internals,
stdlib sort/Vec cost, hashing, process/TLS initial state and panic behavior need
explicit semantics; deterministic Rust output is not a proof of their costs.

| Kernel | Source inputs controlling local trace | Additional obligations |
|---|---|---|
| SeedExpander / Profile21 m31 | public domain, seed, current counter/block/word, candidate words; cap 16 | hash-source relation, refill/cursor across four limbs and failures |
| two-seed nonzero | public nonce, ordered 64-byte OS draws/statuses; cap 16 | byte comparison cost, short-circuit second seed, failed draws |
| division / gamma / circle | raw 32-byte FS answer, public circle row | quotient operands, gamma carry, inverse/subfield tests and fallback |
| sparse_eq_weights | full ten-coordinate point, including previous challenges and public assignment bits | equality internals; arithmetic kernel trace |
| QueryScan | raw FS block pairs, accepted prefix, draw counter | duplicate search position, extra block boundary and exhaustion |
| multiproof | arity, ordered query indices; node payload excluded from control | well-formedness, node_count, sibling sharing, sort/dedup cost, Vec growth |
| P_R1 | complete R1PublicChallenges, build profile, transport/TLS initial state | actual emit/convert/check arithmetic trace, pivots, early exits, std costs |

These are source dependency classifications, not seven formal refinements.
No direct witness read was identified inside these leaf bodies. Their call
arguments and whether/when they are called can still depend on the witness.
In particular challenge dependence is not the same as independence from the
witness, and private-coin marginal independence is not joint privacy.

## Coupling boundary

`R1Z.ProverCommitQuotientCoupling.completed_view` and `middle_completion`
preserve `view`/`retryTest` after tape completion. Their conclusions do not
retain raw sampler words or a source-cost trace. `meanM_Q` proves the completed
middle tape law, not equality of the real source trace paired with that tape.
`R1Z.SideChannelL1JointCoupling` explicitly leaves concrete joint agreement
open. `SideChannelEntropy.count_history_preserved` preserves draw counts,
not short-circuit byte positions under arbitrary successful-seed permutations.
Thus none can be used as an unconditional joint-input coupling for this task.
No freshness, independence or cost premise is silently added.

## Build availability

The documented launcher path without `/tools/` is absent. The existing
`/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh`
accepts only J5000–9999 (literal shell case), whereas this task owns J11400–11599.
No launcher was changed or copied. Lead was asked for a configured launcher.
A local `lake env lean --version` in AspisFormal started a cold mathlib clone;
it was immediately interrupted before any build. Focused Init-only modules can
use the installed 4.32 toolchain from the worktree root without that package.

## Stage 2: checked model results

`lean/R1Z/L2Leaf_Trace.lean` supplies executable reference observations for
zero/nonzero short-circuit comparisons, seed-pair validation, expander refill
and bounded rejection, division operands, gamma carry, sparse suffix/row
selection, QueryScan duplicate search/block control, and binary sibling
sharing. Circle arithmetic and whole P_R1 remain explicit semantics parameters;
they are not discharged implementations. Collection events do not describe
stdlib internal cost. Weight arithmetic, hashing, validation, sorting,
node_count and allocation-failure behavior need their own joins. Consequently
these are **partial reference traces**, not full native source observations.

Checked counterexamples: `nonzero_verdict_not_trace` and
`accepted_value_not_trace`. Both refute replacing trace-input equality by
success/output equality. These are concrete leaf-model counterexamples to a
proof inference, not witness-dependent valid-spend attacks.

`L2Leaf_JointCount.joint_trace_count_bound` proves the finite event-count
coupling bound for the published view paired with arbitrary trace
postprocessing. Both inequalities use the same bad-event count once.
`joint_trace_count_exact` proves exact joint event-count equality if both
view and full input agree. Dividing by the nonempty equiprobable carrier's
size gives the corresponding probability inequalities. No concrete raw-input
agreement, uniformity, native refinement, or R1 epsilon bound was discharged.
No new probability assumption was added, and no old assumption was removed.

Both new modules compile with installed Lean 4.32 and Std only, from the
worktree root using `elan run leanprover/lean4:v4.32.0 lake env lean -M7000`.
This is focused local model evidence, not the coherent env-J release replay.
Every theorem has a printed axioms result; accepted sets are subsets of
{propext, Classical.choice, Quot.sound}. Final local module receipts include
wall, RSS and swaps. The first unsuccessful trace compile was not timed;
its missing metrics are recorded explicitly rather than reconstructed.

Host launch is independently confirmed blocked: `sh .../tools/run-joint.sh
11400 R1Z/L2Leaf_Trace J 7000 8` exits 64, “attempt 11400 outside 5000-9999”.
Calling the script directly also exits 126 because it is not executable.
No infrastructure repair was attempted. No env-J Lean compiler ran.

## Stage 3: Kani source-expression results

14 bounded Kani 0.67.0 attempts, seven passing harnesses:

| Receipt | Passing scope |
|---|---|
| kani-04 | 32-byte two-seed logical comparison: source-expression verdict erasure and same-input trace determinism |
| kani-05 | 16-word masked m31 accept/reject schedule, same raw words |
| kani-09 | one binary multiproof parent group, two sorted indices, independent node payloads; same selected addresses/consumed positions |
| kani-11 | one division limb with arbitrary remainder < P and arbitrary u32 word, quotient range/remainder and same-input operand trace |
| kani-12 | one checker pivot decision on the same row value/pivot state |
| kani-13 | one four-limb sparse suffix coordinate, source-expression Boolean erasure and same-input short-circuit trace |
| kani-14 | one QueryScan comparison, same accepted entry/candidate |

Same-input determinism checks are deliberately modest: they do not establish
any coin/challenge distribution and do not establish that a native caller
supplies witness-free inputs. In particular kani-12/14 are elementary local
decision checks, not elimination/search proofs. Only kani-09 varies actual
payload data across runs. Harnesses are proof-local source expressions and
instrumented slices, not Aeneas extractions or cfg(kani) crate changes.
There are no frozen ELF rebuild claims, and no shipped code was edited.

Failed/aborted attempts are retained. kani-01/02 were stopped after 200/135
seconds while expanding Vec-based proof-only observation collectors (not a
memory kill). kani-03 failed an observer memcmp unwinding assertion; the
observer comparison was changed to pointwise checks. kani-06/07/08 timed out
at 120 seconds on the larger contains/division/suffix loops; replaced by
strictly smaller scopes in kani-14/11/13. kani-10 likewise exposed a proof-side
memcmp unwind bound and was replaced with explicit scalar equality. No
unchanged failed job was rerun with more memory or a longer timeout.

Every Kani job ran in its own systemd scope with MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64. No more than four of these jobs
were concurrently populated (32 GiB total caps); process inspection showed no
other Lean/Kani/Rust build process. This work is symbolic bounded checking,
not dense finite-field elimination, a debug Cargo build or a release arithmetic
gate. There is no Cargo target directory. Timed-out GNU time wrappers report
only 2112 KiB for the timeout process; those values are NOT asserted to be
aggregate child peaks. Their true peak is unavailable; the 8 GiB cgroup cap
and zero-swap policy remained enforced. Failed checks are not release evidence.

## Final per-kernel status and handoff

**Full L2 simulatable trace: OPEN for every kernel below.** “Proved” in this
report applies only to the exact model lemmas or small Kani scopes above.

| Kernel | Proved local result | Remaining before kernel closure |
|---|---|---|
| SeedExpander/Profile21 m31 | reference trace; cap-16 raw-word determinism check | actual hash/refill/cursor, qm31 failure prefixes, whole mask request schedule and joint raw-word law |
| two-seed nonzero | logical 32-byte comparison erasure/determinism; counterexample to verdict⇒trace inference | full 16-draw source/OS-status join and seed-namespace coupling preserving byte-position trace jointly with publication |
| sampler division/gamma/circle | reference division/gamma observations; one division-limb check | all pass/carry/circle/inversion/field traces, arithmetic refinement and raw-FS-block coupling |
| sparse_eq_weights | partial row/index reference; one coordinate Boolean/trace check | native full suffix, multiplication/equality internals, caller point derivation and collection costs |
| QueryScan duplicates | one-block reference and single comparison check | full 22-entry/64-draw relation, eight hashed pairs/extra-block state, exhaustion and raw-block coupling |
| multiproof sharing/sort/dedup | sibling reference, one binary-group check with different payloads | native full 16-query/18-level relation, node_count, actual sorting/dedup/Vec costs and failure paths |
| P_R1 elimination/pivots | pivot-decision microcheck; parameterized trace interpreter | complete emit/convert/check trace semantics, challenge-to-matrix refinement, transport/TLS initial state, collections and panic paths |

No direct witness-value control was found inside the listed leaf source
bodies. This is a source review result, not a whole-program noninterference
proof. Witness-bearing callers, invocation prefixes and F1/F2/F4 remain outside
this local result; no shipped code was fixed. No timings are interpreted as a
privacy proof and no L3 result is claimed.

The central missing deliverable is a concrete joint coupling of the retained
public/history view **and full raw trace inputs**, outside the already charged
bad events. The current privacy model's published-view/quotient completion
statements do not furnish that hypothesis. This task establishes no identical
joint trace law and no epsilon bound for deployed execution.

Next: lead supplies the configured env-J launcher, then compile an explicit
privacy-model bridge with the stronger joint-input agreement premise clearly
visible, and discharge that premise (not simply rename it a coupling record).
Independently, replace the partial trace references with complete source
semantics and compose the small checks with loop/source refinements. Do not
rerun the recorded larger failures unchanged.

Budget charged: 5 local Lean compiler invocations / 100; 0 env-J compiler
invocations (launcher rejected J11400); 14 Kani attempts / 60, 7 passing.
No full manifest replay was run because the source/refinement/coupling cone
is incomplete and the assigned host range is unavailable. No pushes, merges,
crate edits, binaries or key cleanup. Stage commits are plain and local.
