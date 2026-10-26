# pv-srcid3 continuation report — blocked on shared Lean infrastructure

Branch: codex/pv-srcid3-20261026. Base: 52a0f8acee (research, includes
pv-srcid and pv-srcid2). This report distinguishes the deployed endpoint from
explicit selected/reference candidates. The privacy target is not established.

## Input condition and caller chain

The excluded boundary is exactly
`PV_Src_RecordReference.Checked.values.2.1`:
`(PV_Src_NativeInput.outputValue i.request).val < 2^30`.
The mapper copies this output into merged[10][1010]. Thus the previous raw
out=2^30 diagnostic is outside this domain; it is not a counterexample to
V152–V154 or the selected-input words row.

The proof-account adapter RealR1_client::prove_for_proof_accounts accepts a
compilation; it does not itself establish the numeric bounds. The planner
`tools/r1-cost-probe/src/bin/devnet_spend/plan.rs` constructs transfer
(input1000, output600, change400) or withdrawal (1000,250,750), calls the forest
entry compiler and propagates rejection before handing the result to the
adapter. The source transfer wrapper rejects output/change >=2^30; the
withdrawal wrapper combines bounded input from validate_common with checked
Nat conservation. Both paths validate pair words and membership. The forest
entry also rejects noncanonical super-root siblings. Canonical BuilderCanonical
witness values are Fin(2^30); digest encoding supplies canonical M31 words.
D162/PV-CLIENT-ROUTE establishes route intent; it is not a proof of arbitrary
caller bytes or an installed RunJoin selection.

## Proved stages

* Generic Checked from successful extracted validate_common, wrapper value
  guards and canonical super-root siblings (PV_Src_CheckedValidation).
* Checked for every encoded canonical instance (PV_Src_CheckedCanonical),
  preserving its RspendPlus request, not overwriting the public output.
* Both fixture pair records and common-validator calls succeed in the extracted
  validator, with matching runtime binding and a fresh spent-nullifier set.
  PV_Src_FixtureCheckedSource derives Checked from these source calls and the
  entry value guards/conservation. Primitive fixture and bank stages are
  inhabited. Supplied compilation/snapshot parameters do not assert full
  compiler success or installed bytes.
* Selected reference words follow Checked; a four-field Remainder fills the
  original five-field PV_Src_Premises. The unchanged BuilderPremises consumer
  accepts it (SelectedFour/SelectedConsumer).
* All successful extracted compiler branches preserve the supplied snapshot.
  Public variant/asset/next-index/frontier and remaining root/frontier interfaces
  are factored in PublicHeader/PublicParts.
* The owned extracted external callback is total, including symbolic scalar
  reduction, block matrices, sums and lanes. The unstubbed shipped=owned Kani
  external harness passes all571 checks, unwind17, no stubs. The source/ref
  connection follows the stated P6/extraction route; no Lean axiom imports a
  tool result. Exact matrix=retained modulo copy and canonical output lanes
  are also proved for arbitrary inputs (ExternalMat4Copy/ExternalCanonical).

## Family status and exact outstanding interfaces

| Family | Status |
| --- | --- |
| words | REDUCED to actual full Records mapper=owned reference equality plus the installed selected-input encoding; Checked is discharged on the canonical encoding and both fixture source-validation carriers |
| publicCorr | REDUCED to canonical snapshot/root encoding selection and the pure pair_empty_roots result equation; pure sub-obligations are separated |
| compile_call | OPEN for full forest compiler success; ExternalLinear source/ref callback boundary discharged; Records source/ref boundary pending |
| admission | REDUCED to BuilderSpendRelation.RspendPlus on `mapPub (canonicalPublic (publicInput selected))` and `BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness records.w))` for successful selected newRecords |
| row_call | REDUCED to `∀ j, transport j = PV_Src_Transport.row j`, the installed transport equality |

Actual deployed PV_Src_Premises fields: **5 → 5**. Selected/reference instance:
**5 → 3**, standard axioms, unchanged consumer (SelectedThree/ThreeConsumer).
The fixed-root reference publicCorr is discharged using canonical frontier
encoding, the frozen root table and the retained compiler-success field.
FrozenStages proves primitive non-vacuity and public correspondence conditional
on that retained success input. The installed full-compiler fixture fibres
remain open. The deployed source join remains required. No endpoint installation
is claimed. No replacement admission or transport premise has been hidden. The three-field
consumer is a compatibility theorem conditional on its Remainder; no full
compiler-success Remainder is instantiated for either released fixture.

## Evidence and limits

Every charged Lean attempt is in attempts.jsonl, including exact target,
exit/wall/peak RSS/swap/revision/source hash/dependency objects/#print axioms.
Individual out/time/sha/source files retain failures as well as successes.
Failed Lean elaborations may print sorryAx as Lean's error recovery; they are
not accepted theorems and must not enter the final accepted-module audit.

Kani invocation commands and harness names are listed before charging in
kani-invocations.jsonl; per-run receipt.json records pinned source hashes,
revision, command, wall/RSS/cgroup peaks/swap and limits. Full mapper run1
hit its480-second review timeout; all four values/path/digest/public projections also reached
their180-second focused caps: no equivalence conclusion from any of these. The external
callback run succeeded. The shipped common-validator gates passed448/451/452 checks for values,
siblings and pair words, unwind33, no stubs. Their wall times were
23.505/21.655/21.897sec; aggregate peaks1029947392/1036906496/1018671104bytes;
swap0. Exact source hashes and revisions are pinned in their receipts.
No row counterexample has been found.

QUIET-WINDOW.md records the25301 quiet-window violation; RESOURCE-WAITS.md
records the immediate second refused reservation. Neither is concealed by
successful theorem results. No wallet key was created or destroyed.

Next deliverable: restore the authorized pinned Lean cache/launcher, compile
CanonicalNormalize/PackedSelection/CanonicalTransferRecord and perform one final
import/axioms replay; discharge the actual full-mapper P6 equality, then attach
installed selection/RspendPlus/transport at the exact interfaces above.
Frozen-reference public correspondence and the unchanged consumer are already
compiled, not future deliverables.
The current receipt audit covers55 accepted modules with standard axioms only
(accepted-axioms-audit.json), each matching its tested source hash. This is
not a new kernel replay. Shared Lean cache and launcher disappeared at19:50UTC;
HOST-CACHE-MISSING.md records the exact error and the lead-restoration request.
Seven Lean attempts remain uncharged; three further source drafts await the
restored environment. Kani is now12/12, all completed. New Lean89 plus predecessor4 =93/100;
7 remain uncharged. The final roots-only unstubbed check timed out180.008sec,
aggregate peak2510073856bytes, swap0. No unchanged failed gate was retried
with a larger cap. No Kani configuration failure occurred.

The12 Kani invocations comprise2 metadata compiles,4 successful verification
harnesses (external and3 common-validator projections), and6 timeouts
(full mapper,4 mapper projections, full root helper). No checked row
counterexample was found. BUDGET.json and RECEIPTS.md summarize the exact runs.

Work is blocked rather than complete: the final read-only host check still
found the shared source cache/launcher absent; all own scopes are inactive.
The local-lean rule5 prohibits repairing infrastructure, and LEAD ruling(c)
requires useful compile-free work meanwhile. That work and all12 Kani runs are
now finished. The remaining7 Lean attempts cannot be spent on genuine project
checks until the lead restores the authorized environment. The task cache is
retained for the pending continuation. No blanket cleanup or key deletion.

Three uncompiled drafts and the prepared final import/axioms audit are retained
as `.lean.txt` under pending-proof-sources; they are excluded from the formal
module tree and all claims. No final manifest replay was run. The55 accepted
module sources all match successful focused receipts with standard axioms.
The final kernel audit/replay remains a required next step, not an implied
consequence of the receipt audit.

Read-only RunJoin cross-check: runjoin-read-only.json pins the other branch
revision and SourceBoundary/SourceEndpoint blobs. SourceEndpoint explicitly
retains an `inputs` family and world/observer data, rather than installing a
PV_Src_NativeInput.Input selection. No foreign-worktree file was edited or
copied into the proof dependency cone.


## Commit history and resume order

`COMMITS.txt` records `git log --oneline 52a0f8acee..HEAD` through the last
proof/harness commit; the final evidence commit follows it. No push or merge.
Production-source audit confirms no change under crates/ or programs/. All
Rust additions are reachable only under cfg(kani); release implementation and
reviewed soundness/ledger files were untouched.

Resume with next unused Env-J ID25402. Restore the pinned shared sources and
objects (do not cold-build/recreate shared infrastructure in this worker),
copy pending CanonicalNormalize into the module tree and compile it first;
then PackedSelection, CanonicalTransferRecord, and the final accepted-module
import/axioms audit. Seven attempts remain; no Kani invocations remain.
A broader manifest replay needs the approved restored environment and budget.
The full source Records equality still requires a new symbolic/compositional
solution to the actual root helper, respecting the unstubbed P6 requirement;
raising the cap or rerunning the same aggregate is not the next step.
