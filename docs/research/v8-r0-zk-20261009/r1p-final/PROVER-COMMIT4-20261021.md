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
explicit unwind bound and unwinding assertions remain enabled. Status pending.

## Checklist and final evidence

Pending; no complete checklist row is claimed discharged by this setup stage.
