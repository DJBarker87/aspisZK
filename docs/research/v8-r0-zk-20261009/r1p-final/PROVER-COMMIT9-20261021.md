# Prover commitment continuation 9 — 2026-10-21

Branch `codex/cx-prover-commit9-20261021`, base `1be134246`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit9-20261021/`.

## Stage 1: recursive owned balancing

The reference now recurses over ascending rows with a fresh owned accumulator.
It visits exactly the same 1024 rows, uses the existing row transitions, and
retains the shape checks and final dependent-cell assignment. Shipped code
is unchanged. This replaces the continuation-8 loop-context collapse; the
failed lowering is not rerun.

The new extraction succeeds: Charon exit 0, 23.639 s, 670352 KiB peak RSS,
zero swaps, `has_errors=false`; Aeneas exit 0, 0.341 s, 67760 KiB, zero swaps.
Both field additions and subtractions are concrete extracted definitions.
There is no external-function template or unproved arithmetic summary.
The generated Funs is adopted verbatim. Types receives only the documented
explicit discriminant-instance port (`extraction/types-port.diff.txt`).

`ProverCommitBalanceRecursion` proves that each extracted recursion equals
its finite ascending fold for every start row and remaining count whose sum
is 1024. Indexing and arithmetic fail/div are retained. `sequence_ascending`
proves the exact natural row order and bounded nonwrapping successor.
`m31_owned_fold` and `qm31_owned_fold` identify the **whole extracted owned
callers**, including guards and the final write. No concrete 1024-row term
is normalized. Eight printed axioms audits use only standard axioms.

Kani reruns the two row comparisons against the reshaped-reference source:
M31 exit 0, 10.093 s, 531984 KiB; QM31 exit 0, 3.791 s, 488276 KiB; both zero
swaps. They execute the shipped filter/fold transition and compare the
reference step with arbitrary accumulator, value, activity, row and dependent
index. Together with the recursion proof these certify the row/iteration
algebra. They do not themselves certify the shipped Rust outer producer,
its complete coordinate projection, or the endpoint's independently supplied
decoder. No whole-program Kani certificate is claimed.

J8281 Types and J8282 Funs pass. J8283 is an excluded elaboration draft:
the platform-word size bound needed the symbolic `le_numBits` lemma.
J8284 passes the six recursion/order lemmas; J8285 adds the two whole-owned
caller theorems and passes (1.54 s, 2580572 KiB peak RSS, zero swaps).
Exact targets, source SHA, dependency fingerprints, source base revision,
exit, wall, RSS, swap and full axiom/error output are in the Lean JSONL
and verbatim logs. No shared existing source/object is replaced in this stage;
only the new Balance9 namespace is installed. Own new theorem replacements
are snapshotted by the launcher.

Every host gate uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64. Rust uses four jobs and the required four-thread linker flag.
The fresh source workspace reuses this worker's pinned compiler caches.
Reservation receipts enforce the 55 GiB aggregate cap. No wallet key is
created or removed.

## Stage 2: exact D112 caller interface

Work in progress; no caller premise has been removed.

## Stage 3: universal shipped reads and headline

Work in progress; no shipped read-coverage premise has been removed.
