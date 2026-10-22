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

J9743 transports the checked CM31/QM31 arithmetic to the retained canonical
arithmetic results. J9746 proves checked embedded WideExact add/mul closure.
J9749 proves successful checked scalar operations equal wrapping operations.
J9754 composes that relation through all needed field layers, including the
actual release WideExact multiplication. J9756 discharges the checked-success
intermediate: actual release `from_qm31` normalizes every raw input and
preserves its exact value; actual release add/mul preserve the canonical
QM31 embedding and have the expected exact field value. No checked-success
premise remains in `ProverCommitNativeOps47.add_exact` / `mul_exact`.
This replaces the timed-out direct multiplication gate with kernel proofs
over both extractions; no larger cap or unchanged retry is used.

The release serializer's external templates are not installed. D157 is not
used to assert a source arithmetic or payload-image law. No std field has
been added in this stage. Only new task-owned source/object overlays have
been installed; previous versions are snapshotted in the branch workspace.

## Stage 3: complete owned evaluator and canonical limb image

The D144 counter references are in `pair-owner/lib.rs` and
`basis-owner/lib.rs` in this task's evidence directory. Each loop is a
separate recursive function over owned arrays and a decreasing counter.
Charon/Aeneas accepts both. Their extracted field callees are rebound to
`AspisR1ProducerRelease47` only after `bind-counter.py` / `bind-basis.py`
compare every reused declaration body byte-for-byte; the bindings and full
generated inputs are retained. No external template or new std field is used.

`ProverCommitPairCounter47.source_finite` and
`ProverCommitPairValue47.source_value` prove all 512 pair iterations,
including every array index, canonical arithmetic result, and exact decoded
dot product. `ProverCommitBasisMath47.block` proves the symbolic next-block
identity. `ProverCommitBasisCounter47`, `ProverCommitBasisFillValue47`,
`ProverCommitBasisStep47`, and `ProverCommitBasisValue47.values_exact`
prove the nine-stage basis reference produces canonical values equal to
`naturalLineValue` at every one of its 512 positions. No Finset.univ or
concrete 512-step recurrence is reduced.

`ProverCommitY1Owner47.raw_value` composes these owners with the retained
natural-basis model. Every raw coefficient/point family is normalized by
the proved constructor; the result is canonical and decodes to the model's
message evaluation. It has no codec-success, source-success, basis-value
or caller-equality premise. It is explicitly an **owned-reference theorem**:
it does not assert identity with `sim::opening`, the native iterator loops,
the concrete simulator tape, or the complete model payload.

`ProverCommitWordBytes47.word` identifies the backend u32 byte encoding
with the retained exact little-endian codec. `ProverCommitLimbBytes47`
proves each canonical source limb's bytes, its complete 32-byte canonical
subfield cell image, exact decoding, and compact-cell equation. The actual
Rust `WideExact::to_le_bytes` byte-order gate also passes for arbitrary
canonical QM31 inputs: 2.863 s, 288704 KiB RSS, zero swap. Its eight limbs
are in the same documented order, with four zero high limbs. This is a
primitive serializer gate, not a generator-payload certificate.

### Failed paths and replacements

The exact original `basis::values`, `encoder::eval_pair`, and
`encoder::eval_message` bodies are retained in the y1 extraction kit.
The generic Aeneas run exits 2 with `Not_found` in
`InterpReduceCollapse.ml:1991` / loop context joining. Specialization exits
2 at the canonicalization closure (`field/wide_exact.rs:287`,
`InterpStatements.ml:759`). Cutting after the point embedding removes that
closure but exits 2 at `eval_pair`'s `chunks_exact(2).zip(basis)`
(`r0/encoder.rs:6`, `InterpUtils.ml:151`). No source-to-owner equality is
invented from those failures. The first kit draft fails Rust compilation
because its function slicer selected `doubled_factor` instead of `double`;
the corrected source and original failure are distinguished.

The first recursive Vec-pop owner translates with a Vec::pop external
template. It is replaced by the owned-array counter above; no std trust
field for a reference-only pop call is added. The separately translated
basis owner is also array/counter-based.

J9764 and J9766 exceed the fixed kernel memory limit (peak RSS 7170100 and
7170508 KiB respectively, zero swaps) in a combined subtraction declaration.
They are not retried unchanged or with more memory. The replacement isolates
the symbolic raw source step (`ProverCommitSubRaw47.raw`) and the four
coordinate equations (`ProverCommitSubDecode47.coordinates`). J9767 and
J9769 check those separately below 3 GiB; J9771 composes them below 4 GiB.
A byte-word draft is rejected by the kernel with a scalar-width application
type mismatch (J9786). The replacement proves a pure `BitVec 32` byte lemma
and only then transports the scalar wrapper; J9788 passes. Rejected drafts,
including their nonaccepted axiom output, remain in the receipts and are
never imported as accepted evidence.
