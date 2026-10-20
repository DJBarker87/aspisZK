# Prover commitment continuation 4 — 2026-10-21

Branch `codex/cx-prover-commit4-20261021`, based on `8c69254eb`.
D92 identifies the byte callback with the model oracle. No SHA-256 property
is assumed or proved. Evidence is collected under
`docs/research/100bit-spend-path-20261013/evidence/prover-commit4-20261021/`.

## Stage 1: shared oracle harnesses

Proof-only modules use one memoised table for both sides, keyed by the
concatenation of hashv slices. New points receive arbitrary 32-byte answers;
repeats receive the stored answer. Collisions remain possible. Capacity and
per-harness query budgets are assertions, not assumptions. Every loop has an
explicit unwind bound and unwinding assertions remain enabled. The initial legacy-output runs are diagnostic only; final structured-output
verification is pending.

## Checklist and final evidence

Pending; no complete checklist row is claimed discharged by this setup stage.

## Stage 2: oracle-parametric Lean refinement

New module `R1Z.ProverCommitOracleRefinement` proves cache evaluation,
cache extension, arbitrary fresh-answer extension, and the extracted mask
block, source block and private-leaf evaluations for **every** byte oracle.
The oracle is a function of concatenated bytes. The cache extension theorem
permits collisions. No SHA-256 property, independent-word law or source
carrier instance is inferred.

Env J attempt 8144: exit 0, wall 2.24 s, peak RSS 4,015,488 KiB, zero swaps.
All six `#print axioms` lines are in `lean/out-8144.log`: cache theorems use
`[propext]`, extracted callback refinements use
`[propext, Classical.choice, Quot.sound]`. Source SHA, dependency fingerprint,
revision and complete resource/audit receipts are in `lean/attempts.jsonl`.
The existing capped launcher was used, with no shared module overwritten.
