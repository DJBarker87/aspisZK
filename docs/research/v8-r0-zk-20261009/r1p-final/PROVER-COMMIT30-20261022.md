# Prover commitment part 30

Branch `codex/cx-prover-commit30-20261022`; inherited source
`e78e2c022fddebb3d379963ea09efbca478664a7`. Target not yet established.
Env J 7868–7999 only, skipping existing receipts.

## Stage 1: isolate the native semantic callee

The first modular gate compares `SemanticTranscript::semantic` directly with
`semantic20::semantic`, before any record-vector lookup or semantic-array update.
It checks exact errors, state and row counter on rejection, three ordered hash
calls and their framing/answers on success, and identical pure sampler inputs
and call counts. The owned finite-field substitution is justified by the
retained `ProverCommitFields29.bounded_owned`; its zero-index and length
preconditions are asserted at the call site. The native validator is expanded.
This is a pending gate, not a verified contract or a completed native refinement.

All harness additions are external, cfg-only host adapters. No tracked file
under `crates/` or `programs/` has changed. Sources, resource receipts and
commands are retained in the part-30 evidence directory.
