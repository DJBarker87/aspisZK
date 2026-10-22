# Part 47: concrete simulator payload byte image

Work in progress. Target not yet established. Branch `codex/cx-prover-commit47-20261022`.

Scope: concrete `sim::semantic` and `sim::opening` bytes, starting with y1,
then complete native simulator payload equality. Stop before FSExperiments
conversion, shippedProverExperiment, joins, or endpoint changes. D159 includes
L1 side-channel observables; the concurrent audit owns that definition.

No shipped file is changed. No new trust item or premise is authorized.
The endpoint before/after snapshots in
`evidence/prover-commit47-20261022/endpoint/` are verbatim copies of part 46.

## Stage 1: producer range and encoding

The raw codec counterexample in part 46 is retained. The actual y1 producer
embeds QM31 messages and point coordinates into WideExact, then evaluates
with addition and multiplication. The required invariant is the canonical
QM31 subfield image, rather than arbitrary codec success.
