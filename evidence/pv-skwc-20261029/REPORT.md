# D492: OWNM witness and combined audit

Branch `codex/pv-skwc-20261029`, candidate/base `fe3404a688`, exact sparse worktree
`/Users/dominic/ZK/.worktrees/pv-skw`. **All five skeletons SATISFIABLE as explicit
model instances. Combined statement/axioms audit PASSED. Privacy target not yet
established.** No deployed-run witness is claimed.

| Skeleton | Accepted witness | Classification |
|---|---|---|
| OWNM `PV_OWNM_V239.restore` | `PV_SKWC_OWNM.satisfiable` | Nondegenerate model witness |
| DIAG file | `PV_SKW_DIAG_FILE.satisfiable` | Nondegenerate model witness |
| DIAG JSON/stdout | `PV_SKW_DIAG_JSON_STDOUT.satisfiable` | Nondegenerate model witness |
| DIAG error/stderr | `PV_SKW_DIAG_ERROR_STDERR.satisfiable` | Nondegenerate model witness |
| L1 count | `PV_SKW_L1.satisfiable`, also `generic_satisfiable` | Recursive-owner model witness |

## Statement and trust audit

`PV_SKWC_OWNM.lean` compiles the corrected inherited assembly, with all imports
at the beginning. Its `satisfiable` existential supplies one pair of inputs and
the conjunction of all five distinct links: ActualInput on both sides,
SourceDense, Transcript879 on both sides, Transcript890 on both sides, and
OwnedPublicPlan on both sides, plus the public/site/column-length joins.
The scalar theorem is `R1Z.PV_OWNN_SourceDense.concrete_source_dense`, using the
actual raw `source222` and concrete decoder. It was not replaced by a chosen
scalar law. `final_links` also instantiates the final site. `nondegenerate`
proves ten coordinates, three wire points and two columns of length 1024.
Native execution and resource functions are explicit models, not deployed
source associations. Both compared inputs may coincide; the carriers and active
calls are nonempty, with canonical zero and one columns.

The four earlier accepted models and their concrete examples are reused from
`evidence/pv-skw-20261029/REPORT.md`: full NativeTrace Nat carriers for DIAG and
a two-attempt recursive owner for L1. The fixture/transfer-13 review there is
unchanged. DIAG has four explicit links per skeleton (twelve applications),
plus three separately audited projection-step laws; this retains the earlier
clarification of the prompt's fifteen-link wording.

The ONE combined audit is `PV_SKWC_Audit.lean`, attempt **69397**, exit **0**.
Its full output is `lean69397-output.log`: all five complete SAT statements,
nondegeneracy statements, original/generic L1 witnesses, OWNM final-site links,
Instance carriers/model definitions and all relevant Link definitions.
Seventeen witness/helper axioms checks passed: OWNM uses only
`[propext, Classical.choice, Quot.sound]`; DIAG and L1 use `[propext]`.
There is no `sorryAx` in either accepted output.

No endpoint premise or trust field was removed, added or changed. Before/after
skeleton and Link statements are identical: only new modules/evidence changed.
The OWNM model non-vacuity obligation and the combined audit are now closed;
actual producer/source associations and the privacy endpoint's deployment
obligations remain. The next substantive deliverable is an honest producer
instance with the required source/run associations, not another model audit.

## Cache reuse, failures and receipts

The staged cache was found in the preceding job's host directory
`codex-pv-skwb-20261029`; no `skwc` host directory existed initially. New private
`codex-pv-skwc-20261029/objects` links reuse it read-only. `reuse-verification.json`
rechecks 1,819 project entries against the earlier h6 staging or successful
restoration receipts, their companions and recorded dependency fingerprints,
and checks external objects against the existing external authority. The
compiler/toolchain is unchanged; the new private package-root prefix selects
identical objects. **Zero dependency objects were rebuilt.** The 38 declaration
bodies already assembled into the uncompiled draft were elaborated as part of
the requested witness module; they were not rebuilt as dependency modules.
`assembly-source-check.json` verifies their original source SHA256 values against
candidate HEAD. The assembly's provenance is the previous `assembly.json`.

69300 failed in the inherited broad `simp` nondegeneracy proof, which attempted
large list expansion and reached maxRecDepth. The replacement uses named
list-length/map lemmas. 69301 then exposed the small remaining goal
`True ∧ True ∧ True`; an explicit constructor proof closes it in 69302.
Neither failed module earns theorem credit; their `sorryAx` diagnostics are
retained as failure evidence. No recursion/heartbeat cap was raised. Every
submitted source hash differs, so no unchanged failed source was retried.
The wrapper checks this job and both earlier SKW jobs; its SHA256 is
`8866e59c0c4a93614eff7d9bc6cf40824477c5d59697ef171e1f729af15ebe84`.
No environment exception was needed in this resume.

| Attempt/target | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| 69300 / PV_SKWC_OWNM | 1 | 6.1875 | 4376528 | 0 |
| 69301 / PV_SKWC_OWNM | 1 | 6.1187 | 4375996 | 0 |
| 69302 / PV_SKWC_OWNM | 0 | 6.3157 | 4420192 | 0 |
| 69397 / PV_SKWC_Audit | 0 | 1.7888 | 4275356 | 0 |

Every `lean<ID>-receipt.json` records exact source/dependency hashes, source
revision, command, exit, timing, RSS, swap and full axioms/error output; submitted
source snapshots and GNU time logs are retained. The focused compile's recorded
revision is 081d41d94a with working proof edits captured by exact source hash and
snapshot; its accepted bytes were committed in 8088aaa7f7 before the audit.
The audit records revision 8088aaa7f7. All four admissions returned exit 0 and
`allowed:true`, with MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64,
Lean -M7000, one scope at a time. No refusal, void launch or transport retry.
`id-preflight.json` found no collisions. Four of twenty Lean attempts used;
zero native/Kani. Work stops because both requested deliverables are complete.
No additional/full unchanged regression was run.

No crates, programs, existing skeletons, keys or wallets changed. No push or
merge. Cache is retained for dependent work under the explicit reuse rule.
Local commits since the candidate are listed in `commits.txt` (the final
receipt/report commit follows that listing).
