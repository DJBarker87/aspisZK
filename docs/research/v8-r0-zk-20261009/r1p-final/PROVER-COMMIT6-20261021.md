# Prover commitment continuation 6 — 2026-10-21

Branch `codex/cx-prover-commit6-20261021`, base `2086caeff`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit6-20261021/`.

## Stage 1: quotient law

`ProverCommitQuotientLaw.mp_completeOrSpare` proves the new middle-tape
law: decode the H1 quotient; on success keep its visible coordinates and
use the independent spare tape's padding; on failure use the spare tape.
This is measure preserving on full tapes. No sampler words are consumed
for completion. Full equal successful fibres imply quotient equal fibres
with constant `card(Padding) * cF`, via an explicit fibre equivalence.
`ProverCommitQuotientStrict.quotient_law_strict` gives a strictness witness:
every deterministic quotient section has quotient fibre size one and
fails every full-tape equal-fibre law.

Accepted env J attempts: 8191 (law, exit 0, 1.80 s, 3,530,900 KiB peak RSS)
and 8193 (strictness, exit 0, 1.60 s, 3,519,504 KiB). Zero swaps; all five
audits use only propext, Classical.choice and Quot.sound. Drafts 8188–8190
failed elaboration and are excluded. Host scopes use MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000. A private copy of
the existing joint launcher changes only TasksMax; its existing MX argument
sets the requested memory limits. Global launcher and peer sources stay
unchanged. Exact source hashes, dependency fingerprints, base revision,
commands, outputs and timings accompany each receipt.

Further stages and the final signature/checklist diff follow below.
