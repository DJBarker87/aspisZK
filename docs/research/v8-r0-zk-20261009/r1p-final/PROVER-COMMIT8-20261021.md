# Prover commitment continuation 8 — 2026-10-21

Branch `codex/cx-prover-commit8-20261021`, base `a9a27745b`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit8-20261021/`.

## Stage 1: symbolic step replacement

The three 600-second comparisons from continuation 7 are not rerun.
The replacement separates scalar transitions, four-coordinate control flow,
and one balancing row from finite iteration. Results and limitations follow
with the accepted receipts. The scalar-step contract passes (16.839 s,
1,898,040 KiB peak RSS, zero swaps, exit 0). It uses the previously verified
next-word contract. It establishes an absorbing success transition and a
single rejecting/accepting transition over arbitrary owned states satisfying
the explicit next-word precondition; it does not assert a full caller law.

The new host workspace reuses this worker's continuation-7 compiler caches
through symlinks. It has its own sources, receipts, worker lock and snapshots.
No peer source or object is replaced. All host gates have MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64, four jobs and the required
four-thread linker flag. Input receipts carry exact source hashes in addition
to the base revision; additive source edits are committed with their receipts.

The scalar next-step certificate replaces the scalar-summary timeout;
`ProverCommitStepLoop.caller_step_induction` proves the extracted early-return
caller equals sixteen applications of the **newly extracted** `try_step`.
It handles arbitrary callbacks, successful absorbing states, rejection and
Aeneas fail/div. The new extraction contains concrete M31/CM31/QM31 addition;
no external-function template is adopted. Two intermediate extractions
retaining opaque addition are excluded. The Types-only port is the existing
explicit discriminant instance migration; its literal diff is retained.

`ProverCommitFourSteps.collect_extracted_steps` proves composition for every
number of scalar calls by induction; `qm31_collect` identifies the actual
extracted tower caller with four such calls, including left-to-right
coordinate order and the exact failure state. Kani independently executes
the actual shipped mask/source `qm31` bodies over an arbitrary shared
four-entry scalar-result/successor-state trace. Both pass. These stubs are
relational inputs, **not** unproved scalar summaries installed as contracts.
The trace allows arbitrary successors and success values; the error value is
the scalar callers' only actual error, `MaskSampleExhausted`. Callback count
and every state field agree on both success and early exit.

`ProverCommitFoldSteps.m31_fold/qm31_fold` lift the extracted row transitions
to every symbolic row list by induction, preserving monadic fail/div. The
single-row Kani checks execute the filter/fold operation with an arbitrary
accumulated sum, value, activity flag, row and dependent index. Both pass.
These prove the iteration algebra; they do not re-extract the previously
unsupported shipped `Enumerate`/`IterMut` outer loops or establish their
source-to-list transport.

| Target | Exit | Wall s | RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| mask four-coordinate trace | 0 | 5.962 | 611700 | 0 |
| source four-coordinate trace | 0 | 8.008 | 715164 | 0 |
| M31 balancing row | 0 | 3.600 | 490376 | 0 |
| QM31 balancing row | 0 | 3.786 | 490824 | 0 |
| final Charon / Aeneas extraction | 0 / 0 | 23.703 / 0.504 | 661108 / 80960 | 0 |

J8268/8269 compile
Types/Funs independently. J8270 scalar induction, J8271 row induction and
J8273 coordinate composition all exit 0, with 17 standard-axiom audits in
total and zero swaps. J8267 is an excluded attribute-port draft; J8272 is an
excluded elaboration draft. An early Rust draft fails to compile the
source seed's `Zeroizing` carrier; a second reaches a small `memcmp`
unwinding assertion. The replacements correct the carrier and set the
32-byte comparison's explicit unwinding bound to 34. No unwinding check is
disabled, no timeout or memory cap is increased.

## Stage 2: caller transport

Pending definition checks and focused proof results.

## Stage 3: universal read coverage and endpoint

Pending definition checks and focused proof results.
