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

## Stage 2: retained global oracle and observer boundary

`ProverCommitMaterialSupport` proves deterministic support through the whole
indexed material-column and padding reference: if two retained callbacks
agree on every domain/seed/counter expander frame, all returned values,
errors and states agree. The hash is never reset between calls, rows or
columns. Scalar rejection, tower coordinate order, collector, column and
padding induction are all included. This is stronger than per-call local
support but remains a deterministic reference result. It neither proves
fresh independent answers nor instantiates the shipped global-window join.

J8382 is an excluded simp-loop draft, fixed by unfolding only the symbolic
zero branch once; no recursion-depth cap is raised. J8383 passes the focused
support lemmas; J8384 adds the whole extracted indexed-column and padding
consumers and passes: exit 0, wall 2.01 s, peak RSS 2587472 KiB, zero swaps.
All fifteen printed audits use only the standard three axioms. The column
result needs only `SameFrames`; padding also states `row.val ≤ 1024`.
These are oracle-support conditions, not a replacement for either headline
execution premise, and do not hide a whole-execution equality.

`ProverCommitObserverBoundary.replacement_changes_history` proves for every
oracle, every existing history and positive query fuel that `.done` and
one query yield different complete histories. `no_unrestricted_history_transport`
then rules out universal suffix-history equality under an arbitrary program
replacement. J8380 is an excluded reserved-token syntax draft; J8381 passes
both audits with `[propext, Quot.sound]`: exit 0, 1.70 s, 3503196 KiB, zero swaps.

This directly tests the endpoint handoff: `RomObserverBin.observerMap`
preserves `source.observe adv` but replaces its query program with the
independently quantified `observer_program adv`. `GamesR1PBin.realGameP`
uses that program on both the rejection and successful-output branches.
The suffix counterexample is an obstruction to inferring complete history
equality for an unrestricted handoff; it is not a counterexample to the
actual privacy bound or to a correctly identified source program. Supplying
the actual program and proving its operational correspondence remains work.
A reflexive coupling of the mathematical constructor would not establish
that the shipped builder/checker/retry execution runs that constructor.

The all-family ledger is retained in `callback-coverage.json`; material
reference support is added without promoting it to shipped callback-log
coverage. Packing, D collection, successful source-seed wrapper disposal,
salts/tree traversal, retries, aborts and callback-history identification
still need actual source joins. Existing local callback checks cannot supply
these by name alone. No peer-owned source-identification, runtime-join or
final-release module is edited.
