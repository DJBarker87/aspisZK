# D490 resume: cache repair and OWNM witness

Branch `codex/pv-skwb-20261029`, base `772e7e7557`, exact sparse worktree
`/Users/dominic/ZK/.worktrees/pv-skw`. **OWNM UNDETERMINED; combined audit FAILED.
Privacy target not established.** All 40 authorized Lean starts are consumed;
no native or Kani scope was launched.

## Results and witness classification

| Skeleton | Status | Classification and theorem |
|---|---|---|
| OWNM `PV_OWNM_V239.restore` | **UNDETERMINED** | Explicit nondegenerate **model witness draft**, not a deployed-run witness. No accepted `PV_SKWB_OWNM.satisfiable`. |
| DIAG file | **SATISFIABLE**, prior accepted evidence reused | **Model witness**, `PV_SKW_DIAG_FILE.satisfiable`. |
| DIAG JSON/stdout | **SATISFIABLE**, prior accepted evidence reused | **Model witness**, `PV_SKW_DIAG_JSON_STDOUT.satisfiable`. |
| DIAG error/stderr | **SATISFIABLE**, prior accepted evidence reused | **Model witness**, `PV_SKW_DIAG_ERROR_STDERR.satisfiable`. |
| L1 count | **SATISFIABLE**, prior accepted evidence reused | **Model witness**, `PV_SKW_L1.satisfiable`; also `generic_satisfiable`. |

The four accepted witnesses, their concrete nonempty examples, statement details
and original axioms checks remain as documented in
`evidence/pv-skw-20261029/REPORT.md`. No deployed-run witness has been established
for any of the five. The prior fixture/transfer-13 review is reused; no new
execution evidence was collected.

The OWNM draft retains the actual raw `source222`, concrete decoder, and
`PV_OWNN_SourceDense.concrete_source_dense`. It does not replace SourceDense
with a freely chosen scalar law. It uses ten coordinates, three wire points,
and two columns of length 1024, with canonical zero and one, at callback and
final sites. Its proposed conjunction contains all five distinct links:
ActualInput, SourceDense, Transcript879, Transcript890, OwnedPublicPlan,
including both left/right applications and the three public/site/length joins.
The execution/resource functions are explicit models, not source associations.
No contradiction or missing mathematical precondition was demonstrated.

## Staging repair and unchanged-source retry

`staging.json` records 1,781 staged objects, companion hashes, the full verified
L1 cache pin, fifteen old-OWN fingerprint reuses, and external-object checks.
Original L1 and DIAG direct import fingerprints were checked before reuse.
The complete L1 cohort includes `AspisV8R17.QM31WordResidues` and its companions,
which the prior audit had failed to find. Objects and available `.server`,
`.private`, and `.ir` companions were staged in one private package root.
The two freshly rebuilt raw-type objects from the earlier SKW job were not
substituted for the incompatible retained L1 cohort. All source files are
read-only inputs; no other job's directory or shared object was edited.

The old 68707 failure was **pre-elaboration environment**, a missing
`R1Z.PV_OWN_Heap` in the selected private package. The recorded correction is
`environment-corrections.json`; the new attempt is **69100**, which compiled the
byte-identical skeleton successfully and printed its complete `restore` statement
and standard axioms. This exercises ruling (u') without changing any Link.

`run.py` retains the failed-source guard across both SKW directories and permits
only explicitly recorded pre-elaboration environment exceptions. Its sha256 is
`24f98661ac84c12448578bb09afa9c2bf083d1271261282f309d20f16c422987`.
ID scanning found no collisions in 69100–69199. Audit 69197 is consumed;
69198–69199 are unused. No admission refusal or void launch occurred.

## Missing cache, proof assembly, and exact failures

After independently verified objects already staged under the L1 cohort were
excluded, **75** pinned-source modules still needed restoration. Their old
objects were absent, including the scalar source theorem. No matching
`PV_OWNN_SourceDense.olean` or final B2 multiplication object was found in the
host offload search. `remaining-plan.json` records the dependency order.
Attempts 69101–69137 restored 37 individual B2 modules successfully.

To fit the remaining proof work into two starts, `assemble.py` formed one new
`PV_SKWB_OWNM` module from the remaining **38 exact declaration bodies**, followed
by the new witness. `assembly.json` records every original source/body hash.
Only import commands were removed/hoisted and original implicit EOF scopes
were explicitly closed. The skeleton and Link definitions remained imported
unchanged. This is a new private proof assembly, not reuse of missing objects
and not an accepted replacement for their original module fingerprints.

Attempt **69138** elaborated the assembled scalar theorem, printing
`concrete_source_dense` with `[propext, Classical.choice, Quot.sound]`, but the
new witness failed: list-membership simplification left `p ∈ []` and `c ∈ []`
branches, and its nondegeneracy proof supplied equality reflexivity where the
simplifier had produced `True`. Its `sorryAx` diagnostic lines are from failed
elaboration and earn **no theorem credit**. The entire failed module is rejected.

Those proof texts were changed to eliminate empty-list membership and close the
small shape goal directly. Attempt **69197**, the single combined statement and
axioms audit over all five witnesses, then failed because my assembly generator
left the four audit imports after declarations: **`invalid 'import' command, it
must be used in the beginning of the file`**. This is my source-generation
error, not an environmental failure covered by (u'). No unchanged retry occurred.
It did not reach the corrected witness or the combined audit output.

The actual two failed inputs are `lean69138-source.lean.txt` and
`lean69197-source.lean.txt`. The generator's import hoisting is now corrected,
and `unsubmitted/PV_SKWB_OWNM.lean.txt` contains that corrected assembly, but
**it has not been compiled**. The four-model-plus-OWNM audit commands are in
that draft. A fresh focused compile and then an accepted combined audit remain
the next deliverables; no new budget is assumed.

## Validation and boundaries

`validation-summary.json` records exact targets, source/dependency/environment
hashes, revision, exit status, wall time, peak RSS, swap, commands and full
axioms/error output for all **40** starts: **38 passes, two failures**. All were
admitted with exit 0 and `allowed:true`, under MemoryHigh 6G, MemoryMax 8G,
MemorySwapMax 0, TasksMax 64, Lean -M7000. Sum wrapper wall time: **54.6733 s**;
maximum measured RSS: **3,122,596 KiB**; every swap count zero. Successful
restored declarations report only standard axioms. The failed assembly's
axioms output is retained but cannot establish an accepted OWNM or closure audit.
No full frozen-manifest replay was launched; the focused witness never passed.

No endpoint premise was removed, added, or changed. No trust field changed.
Before/after skeleton and Link statements are identical. No crates, programs,
wallets or keys were edited. No push or merge occurred. The pinned private cache
is retained for the next dependent check; no repeated rebuild is needed for the
38 accepted restores.
