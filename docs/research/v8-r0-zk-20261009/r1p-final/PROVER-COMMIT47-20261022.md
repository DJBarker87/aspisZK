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

J9693 and J9696 compile the exact-field subfield and evaluator identities.
`ProverCommitEval47.message_model` identifies the natural-basis dot product
with the retained `R0.Chord.evalMessage` at every circle point. The y1 range,
canonical limb tuple, zero high half, full decoding and compact-cell equations
hold for every 29-lane QM31 coefficient family and QM31 point. These are
mathematical producer-shape facts, not yet a native source-to-payload image.

The actual copied Rust field bodies pass Kani `embedded_codec` (6.375 s,
569888 KiB, zero swap) and `embedded_add` (0.723 s, 164212 KiB, zero swap).
`embedded_mul` times out at 180 s, no verdict. It is not rerun unchanged.
The timeout wrapper RSS is parent-only; cgroup peak is retained separately.
No multiplication or whole-generator certificate is attributed to that run.

## Stage 2: extracted primitive arithmetic

The literal release arithmetic/serializer translation succeeds, but exposes
array-iterator and mutable-chunk external templates for the serializer.
Those templates are retained as diagnostics, not installed as axioms.
A second, narrower translation of arithmetic only uses overflow checks and
has no external templates. Checked/release agreement remains a separate
obligation. No unchecked arithmetic result is silently substituted.
