# L1F count links — D472

Branch `codex/pv-l1f-20261029`, candidate base `e22474ea34`, exact sparse
worktree `/Users/dominic/ZK/.worktrees/pv-l1c`. No push or merge.
**Target not yet established. None of the four full native trace links is
closed. No concrete native producer input is installed.**

## What is checked

`PV_L1F_ReturnedCount.source_read` reads **the actual extracted
RetriedProof.attempts.val**, rather than a native event-decoder projection.
Its statement covers the full Result: successful proof, ordinary error,
outer failure and divergence. `finish_read` consumes pv-diag2's
`finish_result`, so diagnostic reporting does not alter this returned record.
`PV_L1F_SourceRead.actual_retry_count` transports the checked source retry
control equation to that field read on the same callback/store inputs;
`reported_source_count` consumes pv-diag2's complete returned-output law.
These are source/model value laws, not an assertion that compiled native
execution has no additional effects.

`PV_L1F_LoggedCount.source_count_entries` couples the actual source field read
to the checked ordered callback-entry length on success.
`PV_L1F_SourceBounds.actual_count_bounds` establishes **1 ≤ count ≤ 8** for a
count read from the source retry, with **no original-owner or event link**.
It uses the symbolic `PV_L1F_RetryBounds.read_bounds` induction, not concrete
normalization of eight prover invocations. This removes the need for an
original-owner hypothesis for this auxiliary numeric guard only; it removes
no deployed privacy endpoint premise.

`PV_L1F_ActualPublication.source_publication_read` gives the exact count and
rejection projections when the success continuation appends its read count
to an independently retained source prefix. It keeps earlier count/rejection
emissions and emits no new returned count on stop/failure/divergence. It does
not acquire that earlier prefix or prove JSON serialization/delivery.

`count-source-reads.json` checks the three immutable `result.attempts` reads
in deployed plan.rs: Accounts::selected, Accounts::publication and JSON.
This is a **selected direct source-text check**, not full plan refinement,
extraction provenance, b3p6-1 reclassification or a native execution.
`retry-source-reuse.json` separately rechecks pv-diag2's unchanged complete
retry/callback source spans and inherited structural control evidence.
Its leaf/Drop/unwind residuals remain. V370 stays at pending D381/D386.

## Each frozen link

| Link | Status | Exact residual |
|---|---|---|
| `PV_L1E_Link_CountAcquisition` | PARTIAL; full link OPEN | Returned field acquisition is checked as above. Still acquire every earlier ordered native count/rejection prefix, including failed/interrupted/divergent paths, into the independent sourceWorld. |
| `PV_L1E_Link_BodyWrapper` | OPEN | Full ordered source/native body/world trace and terminal equality. Result erasure supplies no missing leaf effects. |
| `PV_L1E_Link_OriginalRetry` | PARTIAL; concrete link OPEN | Checked reached-state full logged join; actual reached leaf association, client adapter and world extension remain unconstructed. |
| `PV_L1E_Link_NativeD163` | OPEN | SAME original D163 execution to native world/terminal association and joint original-to-simE/failure coupling. |
| `PV_DIAG10_Link_Sites` | OPEN, owned here with NativeD163 | Joint honest occurrence/variant/site law, on the same original public/coin/history context and charged failure event. Count bounds and single op success do not supply it. |

All these definitions remain byte-identical to candidate `e22474ea34`.
`source-preflight.json` records the frozen-source hashes. No Link was weakened,
no native trace family was defined as its decoder projections, and no new
simulator, witness restriction, failure event or trust field was introduced.

`PV_L1F_ReachedJoin.reached_join` consumes pv-diag10's actual normal-retry
reach relation and proves **full logged events, Result and final callback/store
state** equal the unchanged D163 run when each reached leaf equals its original
lifted owner record. `reached_producer` supplies exactly pv-diag10's
ReachedAttempt criterion under this association. This is a useful local
criterion: unreachable states need no leaf equality. It is NOT an instance
of that association for the deployed honest prover and does not replace or
weaken OriginalRetry or SourceOwner.

`PV_L1F_WorldLog.bind_log` consumes the pv-own world calculus to retain ordered
calls through source composition; failure and divergence retain the actual
post-world and earlier calls. Its log is an explicitly auxiliary projection
of a separately retained full Run, never a replacement observer or native
world decoder. `PV_L1F_WorldFields` records the heap carrier adapter's remaining
allocator/volatile/atomic-order/fence/thread fields. Neither theorem proves
native allocator, destructor, OS or callback adequacy.

The body frontier is concrete: Source070 has 15 opaque Result lifts and
Source069 has 43 (`body-frontier.json`), besides their named source producers.
Their complete Results are checked; the lifts do not assert native event
silence. b3p6's op227 and pv-diag10's scoped op227 exclusions do not establish
these whole masked-attempt, callback, checker, Drop/unwind or client cones.
No incompatible b3p/runjoin object cohorts were combined to assert otherwise.

## Combined statement and unchanged boundary

`PV_L1F_Statements.combined` concludes exactly
`PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE actualCount native`, conjoined with the
**explicitly supplied, unchanged** Sites law and existing all-prefix lossless
native factorization. It retains all four original trace links and Sites as
separate hypotheses. This is conditional composition, not premise removal
by bundling. The original-to-simE joint distributional assertion is still
additional substantive work; the typed COUNT input alone does not state it.

L1_COUNT_TRACE: PARTIAL. L1_ORACLE_PREFIX, L1_TIME_TRACE and
L1_RETAINED_SIDECHANNELS remain OPEN. ORACLE was not started because COUNT
has not closed. D359 remains the pending owner decision wherever a full
joint elapsed-duration law invokes measurements on the throttled host.
Allocation, addresses, durability, clocks, environment and cross-channel
order are retained.

Headline/deployment premises removed/added/weakened/changed: **0/0/0/0**.
Before and after, the actual native acquisition, original joint L1/simE law,
world association and complete honest producers remain required.
V347–V351 remain OPEN/P. T is exactly entropy_law, entropy_kernel, observation.
No honest-native secret-dependent leak or shipped-source counterexample was
constructed.

Two unattempted corollaries, OriginalRead and OriginalSelection, are preserved
as explicitly unaccepted text drafts with zero theorem credit in
`final-source-manifest.json`. Their hypotheses must not be counted as removed.

## Validation


**100/100 Lean starts: 96 pass, 4 fail. Zero native scopes, zero Kani.**

All three reserved checks passed:

| ID | Exact target | Exit | Wall seconds | Peak RSS bytes | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
| 67197 | `PV_L1F_Statements` | 0 | 1.82 | 5109145600 | 0 | `a37ac80e30439e2ffbc6adbb3b16d5be4a12c533` |
| 67198 | `PV_L1F_Axioms` | 0 | 1.77 | 5090480128 | 0 | `a37ac80e30439e2ffbc6adbb3b16d5be4a12c533` |
| 67199 | `PV_L1F_FocusedReplay` | 0 | 1.92 | 5092143104 | 0 | `a37ac80e30439e2ffbc6adbb3b16d5be4a12c533` |

Aggregate per-module compiler wall time: **191.88 seconds**. Maximum peak RSS: **5109145600 bytes**. Swaps: **0**. All scopes used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and Lean -M7000, one scope at a time. Both immediate admission signals were checked in the same launch command. No reservation refusal, cooldown slip, void launch, resource kill or cap increase occurred.

Failures were 67101 (state-map read normalization), 67187 (reserved binder name), 67188 (remaining definitional projection equality), and 67191 (unreduced function application before rewrite). Each failed source was changed and committed before its replacement. Original outputs and source revisions are retained; sorryAx from failed elaboration earns no credit. Replacements passed at 67102, 67189 and 67192. No unchanged failed source was resubmitted.

The 83 absent inherited prerequisites were rebuilt privately and unedited. The initial 1,640-object reuse and supplemental diagnostic/decoder reuse were checked against selected source hashes and complete direct/transitive import fingerprints. The full 5,673-entry h4 external manifest was checked before the first compile. Setup-only input corrections are recorded in setup-notes.json; no compiler ran during them. No shared object or source was overwritten.

Final read-only validation checks **1760 loaded project/own objects**, **4095 dependency edges**, all **5673 external objects**, and exact toolchain `8c9756b28d64dab099da31a4c09229a9e6a2ef35`. All match. The retained effective path is in final-validation.json. Source authority remains EJR/freeze/h5 precedence; no XR import or h5-double-prime source substitution was needed.

All 21 new local theorems plus the combined statement have printed axioms covered by the accepted audit. Every accepted axiom set is a subset of {propext, Classical.choice, Quot.sound}. receipt-ID.json and modules-ID.json retain each exact target, command, exit, wall, peak RSS, swap, source revision/blob/SHA, dependency fingerprint and full axioms output; raw/ retains hash-verified original compiler and time output. final-source-manifest.json separates the ten accepted roots from two unattempted drafts. This is one focused accepted-closure replay, not a frozen privacy release replay.

Stopped because the 100-attempt Lean budget is exhausted. The next concrete deliverable is actual all-prefix count/rejection acquisition and the native body/world producer on the SAME original D163 experiment, followed by its joint simE/failure/site law. The returned record and numeric guard are now checked prerequisites; they do not manufacture that producer.

COMMITS.txt records the candidate-base to proof/audit-source-tip range. No change under crates/ or programs/, protected soundness files, another worktree, observer or simE; no push, merge, ELF rebuild, timing measurement, Kani run, wallet/key/account operation or new trust item. Evidence files are below 20 MiB and contain no binaries or compiler objects. Cache cleanup removes only this job's rebuildable artifacts and links after the validated inventory; sources, receipts and all keys are retained.
