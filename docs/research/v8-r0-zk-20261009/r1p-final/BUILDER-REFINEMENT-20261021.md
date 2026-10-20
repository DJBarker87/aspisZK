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
