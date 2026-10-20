# Builder refinement — 2026-10-21

Branch `codex/cx-builder-ref-20261021`, base `9ba738457`.

## Scope and status

Work in progress. The target is the first open obligation in
`PRIVACY-FINAL-20261020.md`. No deployed closure is claimed by this draft.

## Evidence

Focused env-J attempts use only 8400–8599 and are appended to
`attempts.jsonl` by `builder-build.py`. Existing shared sources/objects are
snapshotted before replacement under the branch name.

## Stage 1: extracted composition

`R1Z.BuilderRefinement` defines `mergedTrace` as the word-lift of
`copyCellMerged`. Its prover's `build` is this trace, not the abstract
`buildModelSpec`. `mergedTrace_eq_model` applies `builder_witness_merged`
extensionally. `sound_merged` and `builderSoundOn` supply baseTyped, lanes,
helperSum and helperInactive via D51 and D43/D42.4.

The theorem is explicitly on `Admitted` inputs (`PubCorr`, `WitnessOk`,
`ModelRel`); deriving these from a successful shipped compile is not proved
in stage 1. The transport is still an explicit parameter.

Env J was missing the model-completeness objects. Attempts 8401–8413
compiled the unchanged prerequisite modules, in dependency order; attempt
8414 compiled the new module (exit 0, 3.26 s, 3,991,752 KiB RSS, 0 swaps).
All axiom audits use only propext, Classical.choice and Quot.sound. The
136-link generator `--check` passed before compiling its chunks.
Attempt 8400 failed on a missing HelperInactive object; it was retried
only after both missing helper dependencies were compiled (new fingerprint).
The host snapshots retain any pre-existing source/object before upload.

## Stage 2: semantic endpoints

`R1Z.BuilderSemanticBridge` proves the block endpoint, owner, nullifier,
three-chunk note, input, recipient, change, node and arbitrary membership
prefix identities against R0P.Semantics. The node proof accounts for the
M31 addition/subtraction tweak. No concrete Poseidon evaluation is used.
Attempt 8438 passes (4.48 s, 3,262,736 KiB, 0 swaps), with all thirteen
theorems axiom-audited. Earlier failed sources (8415, 8416, 8421, 8431)
are retained in attempts.jsonl; the initial whnf timeout was replaced by
explicit state/input projection lemmas and local irreducibility, not a limit
increase.

The canonical spend-relation source closure was absent from env J. It was
compiled from the current repository's canonical lean/ files, using the
existing R1-prefixed module names where their imports require them. The
build receipts record `repo_source` for each promoted alias. The first
AppendPair attempt (8422) exposed the missing V7PairLeafOccupancy object;
8424 builds it and 8425 is the dependent retry with changed inputs.

## Stage 3: Rspend⁺ to ModelRel

`R1Z.BuilderSpendRelation.modelWitness` maps every field of the existing
`AspisR1.SpendRelation.Witness`. `RspendPlus` is exactly Rspend plus D50's
transfer change sentinel. `modelRel_of_spend` derives all semantic ModelRel
fields: auxiliary occupancy/conservation/amount, public digest identities,
append root/carry, and PairRight. It takes only public/witness base-field
membership in addition to Rspend⁺. PairRight is derived from the selected
commitment and first sibling, not assumed.

Attempt 8443 passes (2.12 s, 3,522,140 KiB, 0 swaps), all six theorems use
standard axioms. Failed attempts 8441/8442 were corrected proof sources;
no resource limit changed. This closes T4's semantic relation implication,
but does not yet connect the shipped records function to this witness map.

## Stage 4: canonical inputs and the four fields

`R1Z.BuilderCanonical` defines the canonical RustWitness/RustPublic maps
from M31 public inputs and Wspend, and proves their lifted merged trace
equals the model on the embedded semantic witness. All public/witness
base-membership facts are derived: any subfield contains the image of the
prime field. Its honest instance is a subtype carrying only Rspend⁺ on the
embedded witness and public input, with no ModelRel or trace-validity field.
`builderSoundOn` supplies all four fields for this concrete extracted
builder. Attempt 8444 passes (2.35 s, 4,005,424 KiB, 0 swaps); all seven
theorems have standard axiom audits.

This still is not a theorem that the shipped compiler's successful input
projects to this subtype, or that its Rust structural glue is the extracted
Lean composition. Those are the next source obligations.
