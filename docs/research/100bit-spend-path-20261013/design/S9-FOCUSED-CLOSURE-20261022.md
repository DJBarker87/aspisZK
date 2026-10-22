# Focused S9 closure attempt — 22 October 2026

The previous S4 library/extraction experiment is held before the new Charon
build. The user asked which S is the quickest credible full-cone attempt with
all four slots. S9 is the choice for the unchanged source, based on its small
four-output, two-side helper and existing 56-coefficient identity. This is a
relative judgment, not evidence that closure is assured. The first decision
point is 4–6 hours, not a promised completion time.

The actual closure target remains the delivery table's complete S9 source
join: reached operands, complete checked helper state/output, surrounding
caller and current source pin, sufficient to instantiate the frozen-order
cone. A successful local algebra/helper theorem alone is not closure.

## Parallel work, with one local compile at a time

- D18: derive the N=4 power trace and exact returned helper arrays from
  canonical seeds. Derive success, indexed canonicality and power meanings;
  do not assume independent successful traces or `kpowers` results. Keep the
  outer caller assignment as a separate source obligation.
- Q: install actual current arithmetic methods in one concrete `FieldOps`
  record, including the selected square body rather than a replacement
  multiply-by-self definition. Supply matching method laws to both workers.
- FS: prove the generated helper's exact two-iteration control/state Result,
  then its success and decoded output using those concrete operations.
  Decompose the actual emitted body; do not copy a nicer algebra model and
  label it the source.
- Root: supply the decoded side-update algebra, integrate the helper with the
  existing factored/original formula, and resolve actual caller/source binding.

Reuse owners include `s3-scalar-factor-powers-constructive-s9-v1`,
`s3-kpowers-total-and-s9-no-premise-v1`, `s3-s9-helper-p6-ops-v7`, the current
field-operation owners, and `S2LibraFactoredIdentity`. The retained helper
source-cut's **Pair method is a normalized candidate**, not the frozen caller.

## New proved component

`evidence/s9-focused-side-updates-root-v1-20261022/` contains
`AspisR1.S9SourceSideUpdatesRootV1.two_side_updates_eq_factored` and
`two_side_updates_eq_original`. They identify the decoded square/multiply
chain, high terms, and exact two-side writes with all four model outputs.
Every old output cell is arbitrary: the complete schedule overwrites them.
Zero challenges are included. No successful-helper hypothesis is introduced.

Focused Lean 4.32 compile: exit 0, 6.576 s, process RSS 1,504,296,960 bytes,
observed swaps 0; standard axioms only. Exact receipt, imports, source pins and
failed first attempt are retained. The original/factored identity is reused.
The current complete helper body matches its retained extracted source-cut
body, SHA-256 `741b0a147a82edfbc47b363e50e5163662cd82be8af21f769699e1d3c9506f2a`.
This is decoded algebra, not yet execution refinement.

## Unresolved boundary and stopping rule

S9 still calls Rust `core::array::from_fn`, both through powers and to build
high terms. Existing P6 models prove ordered value semantics but do not prove
the frozen Rust initialized-buffer, ownership/drop and final array conversion
semantics. The extracted full Pair candidate also does not prove the current
source caller. These cannot be hidden in a record or treated as cryptographic
assumptions.

Do not restart the generic compiler campaign inside this attempt. Establish
how far the concrete helper can be proved, then expose the smallest remaining
library/source obligation. If that boundary prevents a complete cone, report
it and propose a narrow proof-friendly source change with its affected pins
and gates. Adoption remains governed by the freeze/B1 decision; PR #10 is
still unadopted. S9, the global source join, and implementation-linked
100-bit per-attempt soundness remain OPEN.
