# Prover commitment continuation 14 — 2026-10-21

Branch `codex/cx-prover-commit14-20261021`, base `3bbbd12bb`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit14-20261021/`.

The actual release target is not yet established. This report is updated by stage.

## Stage 1: owned indexed material schedule

The proof-only reference adds `material_columns_owned`, `collect_qm31_owned`
and `material_padding_owned`. Fresh owned vectors and expander state cross
recursive calls. Columns retain their initial vectors, append exactly 1024
scalar results, then balance before the next column. Padding skips active
and dependent rows; errors retain the state and partially written values.
The caller must supply initial empty columns, correct remaining count and
valid dependent/layout indices. No production body or Cargo input is edited.

Charon/Aeneas v1 both pass (23.684/0.622 s, 681368/92576 KiB, zero swaps).
V2 makes the column count explicitly decreasing so the finite induction
requires no hidden length-preservation premise. Charon/Aeneas v2 both pass
(23.893/0.658 s, 673080/92576 KiB, zero swaps). All field operations are
translated concrete bodies, not opaque summaries; no external template is
introduced. Types receives the same explicit discriminant port as part 9.
Generated Funs is adopted verbatim. Original generated text and tool hashes
are retained in extraction evidence.

`ProverCommitMaterialRecursion.extracted_finite`, `qm_extracted_finite`,
`columns_extracted_finite`, and `padding_extracted_finite` identify each
whole extracted recursion with its symbolic finite schedule, preserving
allocation/indexing/scalar/balancing failures. Padding requires
`row.val + n = 1024`; columns require `remaining.val = n`. These are
reference theorems, not a source-to-model execution join.

J8373 Types and J8374 Funs pass. J8375 checks both scalar collectors.
J8376/8377 are excluded column-induction elaboration drafts; J8378 checks
columns; J8379 checks all six final theorem audits, exit 0, wall 2.05 s,
peak RSS 2596212 KiB, zero swaps. All accepted printed axioms are a subset
of `[propext, Classical.choice, Quot.sound]`. Exact modules, source hashes,
dependency fingerprints, revisions, errors and full audits are in the Lean
JSONL and verbatim logs. No failed draft is adopted as proof evidence.

The Kani one-iteration comparison is in progress at this stage commit.
The material schedule has not yet been identified with the entire shipped
builder or canonical raw-array projection. No endpoint premise is removed.
