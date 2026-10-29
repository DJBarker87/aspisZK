# D487: skeleton integrity audit

Branch `codex/pv-skw-20261029`, base `7d8769c123`, exact sparse worktree
`/Users/dominic/ZK/.worktrees/pv-skw`. **Partial result: four model SAT witnesses;
OWNM UNDETERMINED. Combined audit FAILED. Privacy target not established.**

## Results and statement audit

| Skeleton | Status | Accepted theorem and evidence |
|---|---|---|
| `PV_OWNM_V239.restore` | **UNDETERMINED** | No accepted `PV_SKW_OWNM.satisfiable`; draft is under `unsubmitted/`. The pinned `SourceDense` law was retained in the draft, never replaced by an arbitrary scalar function. |
| `PV_DIAG10.DIAG_FILE_TRACE` | **SATISFIABLE**, explicit nondegenerate model | `PV_SKW_DIAG_FILE.satisfiable`, `nondegenerate`, `project_step`; attempt 68708. |
| `PV_DIAG10.DIAG_JSON_STDOUT_TRACE` | **SATISFIABLE**, explicit nondegenerate model | `PV_SKW_DIAG_JSON_STDOUT.satisfiable`, `nondegenerate`, `project_step`; 68709. |
| `PV_DIAG10.DIAG_ERROR_STDERR_TRACE` | **SATISFIABLE**, explicit nondegenerate model | `PV_SKW_DIAG_ERROR_STDERR.satisfiable`, `nondegenerate`, `project_step`; 68710. |
| `PV_L1E_OriginalCountSkeleton.original_count_trace` | **SATISFIABLE**, explicit recursive-owner model | `PV_SKW_L1.satisfiable`, `nondegenerate`; 68704. `generic_satisfiable` also covers the four links of `PV_L1E_CountSkeleton.count_trace`. |

Each DIAG witness has the exact form
`∃ x : Instance, Link_Init x.state (project []) ∧ Link_Step x.state join single ∧
Link_Readout x.actual x.state x.raw ∧ Link_EventOrder x.raw x.native`.
The skeletons have **four** explicit link hypotheses each, hence twelve link
applications, rather than fifteen distinct DIAG links. The three additional
projection-step laws are separately proved, accounting for fifteen checked
conditions if those internal laws were intended by the prompt.

The carrier is the entire `NativeTrace Nat` type, not Empty, Unit, or a singleton.
It includes arbitrary event lists, byte payloads, finite prefixes and all terminal
forms. The concrete file example has two nonempty writes; JSON/stdout has a
nonempty JSON payload and stdout delivery; error/stderr has a Semantic error and
a nonempty fd-2 request with failure terminal. State accumulates the corresponding
projection on arbitrary event prefixes. These models prove consistency of the
interfaces; defining model observers this way does **not** associate any deployed
observer or discharge the actual producer links.

The original COUNT witness has the exact four conjuncts CountAcquisition,
BodyWrapper, OriginalRetry, NativeD163, with the same `owner`, `run`, initial
state, fuel, index and adapter on both joins. Its carrier is `Nat × Nat` for fuel
and index; state and proof carriers are Nat. The owner rejects at index zero,
then succeeds, advances state, and retains attempt records. `nondegenerate`
checks actual count/rejection output `([2],[0])`, post-state `2`, and successful
proof `2` at `(fuel,index)=(2,0)`. The adapter reads the actual recursive model
run; it is not a fixture or source-binding certificate. The generic COUNT
conjunction is also witnessed with the same trace families. No carrier was
chosen empty or singleton, and no empty output was used to hide an active link.

## Why no honest-run claim

`fixture-review.json` lists the canonical pv-2tnv witness and transfer-13 records
read. The canonical witness inhabits a spend-plus builder fibre. The transfer-13
manifests are historical SVM verifier/CU comparisons, not current-prover observer
or allocator traces. They do not provide the joint ordered raw/native event and
observer-state families, raw op222 arrays, or owned point_claims ResourceExit
family needed here. The accepted witnesses are therefore explicitly model
instances, not deployed/fixture producer instances.

## Exact OWNM obstruction and failed attempts

The old OWNM/OWNN objects had been removed. Seventeen objects in its cone were
reusable; a read-only pinned-source replay plan identified 78 missing objects.
All 188 ownc/ownn source pins checked byte-for-byte against candidate HEAD
(`candidate-own-pins.json`). The two raw type files compiled at 68705/68706.
At 68707, the **unchanged skeleton** failed because my private package staging
left `R1Z.PV_OWN_Heap.olean` outside Lean's selected private package directory.
This is a staging mistake, **not a proof of contradiction**.

Ruling (u)'s exact source-hash guard prevents resubmitting this failed source;
the prompt also prohibits editing the skeleton, including changing its source
to evade the guard. I requested a one-time environment-only retry exception,
but received no exception during this run. The guard is tested without launching
a compiler (`guard-test.json`); its hash is in `validation-summary.json`.
The remaining OWNM proof was not launched or credited. Its draft uses the real
concrete decoder/source law, ten coordinates, three wire points and two
1024-row columns, but is **uncompiled**. No mathematical contradiction was found.

68700 failed on my reserved identifier and append proof; changed witness text
compiled at 68701. Later nonempty examples changed those sources before 68708–10.
The audit at 68797 failed on a missing `.olean.server` companion; 68798 failed
on dynamic import `AspisV8R17.QM31WordResidues`. The retained complete L1 cache
then exposed a hash conflict with the freshly rebuilt `R1Z.ProverRwFullTypes`.
Both source hashes agree, but object hashes differ (`cohort-conflict.json`), so
this is **not evidence of a source/type contradiction**. No conflicting object
was substituted. The final audit 68799 again failed on the missing dynamic
import. All three reserved audit IDs are consumed; none earns audit credit.
The sources changed between these audit attempts; no failed source was rerun.

Next deliverable: obtain the explicit unchanged-source retry exception and fresh
audit IDs; isolate OWNM and L1 package roots, restore all pinned object companions
and dynamic imports, compile the pinned skeleton and remaining source-law cone,
then type-check the OWNM conjunction witness and replay both audits. Do not edit
any existing link. The cache-staging scripts here are task inputs, not validated
replacement launcher infrastructure.

## Axioms audit and validation

Focused, accepted `#print axioms` outputs cover **all twelve new accepted
propositions**: three SAT, three nonempty examples, three projection-step laws,
and original/generic COUNT SAT plus its nondegenerate run theorem. Every one
reports **`[propext]` only**. No accepted output contains `sorryAx` or a new axiom.
See 68704 and 68708–10 output logs. Statements were type-checked in those focused
compiles, and their exact conjunctions are in the accepted source snapshots.
**The combined statement/axioms/import audit did not pass**; the failed final
manifest is retained only as evidence, not a closure result.

`validation-summary.json` records all 14 actual Lean starts (9 passes, 5 failures),
targets, exit statuses, source revisions/hashes, wall time, peak RSS, swaps and
axiom lines. Total measured wrapper wall time 10.04 s; maximum RSS 4,288,136 KiB;
all swaps zero. Every scope was admitted with exit 0 and `allowed:true`, capped
6G/8G/swap 0, TasksMax 64 and Lean -M7000. No admission refusal, void launch,
native scope, Kani run, or local Lean compile occurred. Budget unspent because
of the unchanged-source prohibition and exhausted reserved audit IDs, not
because the Lean attempt budget was exhausted.

No existing skeleton, Link definition, crate, program, wallet or key was edited.
No endpoint premise was removed or added, no trust field changed, and no source
association was installed. Before/after link statements are identical. Four
model non-vacuity obligations are discharged; OWNM and the combined closure
audit remain open. Commits are local only; no push or merge.
