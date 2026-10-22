# Focused S9 closure attempt — 22 October 2026

The previous S4 library/extraction experiment is held before the new Charon
build. The user asked which S is the quickest credible full-cone attempt with
all four slots. S9 was selected before the S4 adoption, based on its small
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

After the S4 adoption, WideExact powers uses the indexed early-return body.
S9 still calls Rust `core::array::from_fn` through QM31 `kpowers` and to build
high terms. Existing P6 models prove ordered value semantics but do not prove
the frozen Rust initialized-buffer, ownership/drop and final array conversion
semantics. The extracted full Pair candidate also does not prove the current
source caller. These cannot be hidden in a record or treated as cryptographic
assumptions.

Do not restart the generic compiler campaign inside this attempt. Establish
how far the concrete helper can be proved, then expose the smallest remaining
library/source obligation. If that boundary prevents a complete cone, report
it and propose a narrow proof-friendly source change with its affected pins
and gates. PR #10 was adopted at `29cbab431` after explicit user approval of up to
12,000 additional CU per transaction. See S4-ADOPTION-DECISION-20261022.md.
This removes the original WideExact powers from_fn obligation; it does not
remove the separate QM31/high-terms library boundary. S9, the global source join, and implementation-linked
100-bit per-attempt soundness remain OPEN.

## Concrete operation progress

The focused concrete record is now green in
`evidence/s9-focused-concrete-fieldops-v1-20261022/`. It installs actual
selected/current operation calls, including the square body, wide product,
add, M31/mixed products and extracted fold. The square and mixed-product
meaning/totality continuation is separate; record dispatch is not counted as
proving those laws.

`evidence/s9-focused-mulm31-total-root-v1-20261022/` closes the previously
success-conditional wide-by-M31 leaf: actual QM and wide calls are now proved
total for every stored input; the concrete S9 record returns a canonical,
exact scalar product on canonical input. No successful multiplication is
assumed. This reuses the existing total U32 reducer and exactness owners.
Focused exit 0, 19.737 s, process peak 3,153,149,952 bytes, observed swaps 0,
standard axioms only. The packet explicitly records incomplete historical
cross-session mutex evidence rather than claiming stronger resource control.

The emitted helper's structural two-step proof, full arithmetic composition,
reached power-array consumer and source/caller boundary remain in flight.
No complete cone has been declared closed.

## Reuse correction and subsequent checked consumers

The generic arbitrary-input M31 totality lemma already existed in
`AspisR1S3PowersLowTotalV1`. The first root packet duplicated its proof;
those primitive lemmas must not be counted as newly closed arithmetic.
The preferred consumer is now
`evidence/s9-focused-mulm31-reuse-root-v2-20261022/`, which directly imports
that owner and proves totality/exactness for the same concrete S9 callback.
The historical first packet has an explicit correction. One focused replay
of V2 repaired missing clean concurrency evidence after a sibling mistakenly
launched a second Lean process; all local launches are now centralized with
ownership/foreign-process monitoring. No unchanged full regression ran.

Further checked packets, all with standard-only theorem audits:

- `evidence/s9-focused-powers-v1-20261022/`: from canonical seeds, construct
  the low N=4 P6 trace/mapped array and actual concrete `kpowers` output;
  all returned entries have canonicality and indexed power meanings.
  Independent low/high successful-call premises are not assumed. The outer
  caller assignment is still separate.
- `evidence/s9-concrete-operation-semantics-v1-20261022/`: actual selected
  square success/canonicality/decode and concrete mixed-product totality.
- `evidence/s9-concrete-wideqm-product-v1-20261022/`: the same constructed
  mixed-product result is canonical and has the exact coordinate products.
- `evidence/s9-wideqm-scalar-product-root-v1-20261022/`: rewrites those same
  coordinate products as multiplication by the QM31 scalar embedding in
  the wide field. No operation-success premise is introduced.

A centrally checked emitted-body control lemma is green in the working
V3 owner: active-body success must return `.cont` with the same next iterator.
Its checked source carve is definitionally equal to the emitted active
suffix. It does not prove body/helper success or decoded output. The
complete two-iteration consumer and high-terms array proof remain in flight.

The generic low-powers source gap has been localized further: the old
full-pair emission declared `weights.powers` externally, and its diagnostic
Rust cut used an unreachable stub. A new narrowly selected NUC extraction
retains the real generic powers function and closure, but its multiplication
shim is still emitted as `fail panic`; that raw output is explicitly rejected
for proof use. A mechanically checked typed-operation/P6 adapter is being
built. No selector retry or compiler rebuild is authorized by this result,
and no frozen Rust Std/array or deployed-compiler correspondence is inferred.

## Adopted-source continuation

The two emitted calls are now proved in
`evidence/s9-emitted-two-step-control-root-v1-20261022/` (commit b8d288ba1):
a successful helper run yields its actual first body call, actual second body
call and terminal iterator result, carrying the same intermediate/final arrays.
This is accepted-run control decomposition, not totality or decoded output.

Current ownership: D18 reuses the generic indexed early-powers theorem for the
actual N=4 WideExact helper array; FS joins the two calls to their actual
scalar-factor results and post-scalar source suffixes; Q joins the four actual
high-term callback results and their exact stateful P6 array; root connects the
checked array writes and branch arithmetic to the retained two-side identity.
Only the root launches local Lean. The shared mutex is respected across other
live Codex sessions; failed attempts and diagnostic axiom reports are not
accepted theorem evidence. No unchanged full replay is launched.
