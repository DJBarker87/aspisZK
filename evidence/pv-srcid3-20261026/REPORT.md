# pv-srcid3 continuation report (working)

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
  tool result.

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
is claimed. No replacement admission or transport premise has been hidden.

## Evidence and limits

Every charged Lean attempt is in attempts.jsonl, including exact target,
exit/wall/peak RSS/swap/revision/source hash/dependency objects/#print axioms.
Individual out/time/sha/source files retain failures as well as successes.
Failed Lean elaborations may print sorryAx as Lean's error recovery; they are
not accepted theorems and must not enter the final accepted-module audit.

Kani invocation commands and harness names are listed before charging in
kani-invocations.jsonl; per-run receipt.json records pinned source hashes,
revision, command, wall/RSS/cgroup peaks/swap and limits. Full mapper run1
hit its480-second review timeout: no equivalence conclusion. The external
callback run succeeded. No row counterexample has been found.

QUIET-WINDOW.md records the25301 quiet-window violation; RESOURCE-WAITS.md
records the immediate second refused reservation. Neither is concealed by
successful theorem results. No wallet key was created or destroyed.

Next deliverable: finish the frozen-reference public correspondence and
unchanged consumer; verify decomposed unstubbed mapper obligations; attach
installed selection/RspendPlus/transport from pv-runjoin at the exact interfaces.
Final budget totals and accepted-module audit are pending.

Read-only RunJoin cross-check: runjoin-read-only.json pins the other branch
revision and SourceBoundary/SourceEndpoint blobs. SourceEndpoint explicitly
retains an `inputs` family and world/observer data, rather than installing a
PV_Src_NativeInput.Input selection. No foreign-worktree file was edited or
copied into the proof dependency cone.
