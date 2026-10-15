# Literal composition checkpoint — 2026-10-15

Four focused targets are checked on top of `3713ceaf4`. They supply exact
representations needed to reuse the existing semantic extraction theorem;
they do not close the accepted-execution or source-refinement obligations.

| Target | Checked result | Wall seconds | Peak aggregate RSS, KiB | Axiom reports |
| --- | --- | ---: | ---: | ---: |
| `SemanticHit` | Import ordering reuses the existing generated congruence declaration; theorem statements and bodies unchanged | 127.127 | 3,700,848 | 2 |
| `LiteralSemanticExcludedLift` | Literal no-hit plus successful readers supplies each semantic exclusion on the lifted parsed list | 139.616 | 3,939,024 | 1 |
| `LiteralOpeningDataRows` | Updating data with its selected functionals leaves the data unchanged | 123.136 | 3,933,024 | 1 |
| `LiteralOpeningFunctionalFacts` | Successful opening reads expose their selected functionals, semantic parse, C1/C2 projections, and literal word | 84.715 | 4,516,016 | 2 |

All four final targets exited zero; all six reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Each external timing receipt reports zero
process swaps. This is not a claim that system-wide swap was zero. The local
runner used the existing compiled cache, Lean's 5,000 MB limit, a monitored
7 GiB aggregate process-group stop threshold, and a 900-second timeout. There
was no cold dependency build or full manifest replay. The user explicitly
selected local work after the NUC became unreachable.

Root independently checked 132 bundle checksums and two reused committed cache-provenance files, each final source against
its frozen attempt, each final object against both its archive and the local
cache, successful receipts, and the final axiom reports. The review record is
`evidence/j1-local-literal-composition-review-20261015.json`. Corresponding
bundles are `lean-semantic-import-join-20261015`,
`lean-literal-semantic-excluded-lift-20261015`,
`lean-literal-opening-data-rows-20261015`, and
`lean-literal-opening-functional-facts-20261015`.

## Reuse and discarded work

The semantic import diagnostic identified `R1SemanticHit` as the owner of a
generated name already owned by `R0P.MaskD2Glue` in the other import branch.
Importing the existing glue before `MaskNoHit` fixes that overlap without
changing the older semantic core. The combined consumer subsequently passed
import loading but did not compile its theorem: its concrete statement hit
a 200,000-heartbeat elaboration timeout. That redundant `LiteralSemanticLiftNoHit`
wrapper was retired. All its attempts and its last source are retained in
the import-join bundle; it is not counted as a checked theorem.

The direct, checked `LiteralSemanticExcludedLift` conclusion already has the
exact per-index exclusion shape required by
`SemanticPrefix.large_matching_extracts_of_prefix`. The terminal composition
therefore uses that result directly. Incoming R7/R8 C2 projection lemmas are
also reused; an earlier duplicate draft was discarded.

## Still open

The conditional terminal composition and its remaining parser/data helpers
are being checked separately. `Good`, accepted-pairing equations, the large
matching-set bound, and semantic check equations must be supplied by their
stated hypotheses or checked adapters. Literal reader success does not by
itself imply acceptance. No current theorem here identifies the production
Rust verifier's acceptance with those conditions.

Current source/runtime refinement, commitment cuts, concrete sampler and
input-bound correspondence, executable extraction obligations, and the final
runtime/artifact checks remain open. The other session owns the R11/R12 Rust
changes and their merge. This checkpoint makes no new end-to-end security,
privacy, compute-unit, or deployment claim.
