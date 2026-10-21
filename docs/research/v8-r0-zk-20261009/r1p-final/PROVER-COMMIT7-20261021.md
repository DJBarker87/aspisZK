# Prover commitment continuation 7 — 2026-10-21

Branch `codex/cx-prover-commit7-20261021`, base `072b24afc`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit7-20261021/`.

## Exact cursor classification

`ProverCommitCursor.decoder_exhausted` identifies failure of the finite,
consuming sequential array decoder with `CommitReadsR1.Exhausted` whenever
`16 * L ≤ N`. The proof handles arbitrary word streams and every starting
cursor/retry state. It does not pad accepted limbs to sixteen words. It
proves the forward/reverse Kleisli iterations equal and transports the
finite suffix recursion to the actual `tryLimb`/`limbPos` definitions.

Focused env J **8243**: exit **0**, wall **2.09 s**, peak RSS
**4,034,836 KiB**, **zero swaps**; five verbatim audits use only
`propext`, `Classical.choice`, `Quot.sound`. Attempts 8240–8242 were
elaboration drafts, excluded. An unchanged-input preflight for 8243 was
refused before compilation; the proof was then corrected and 8243 used
normally. The refusal is not accepted verification evidence.

Further stage results, exact checklist changes and final audit follow below.
