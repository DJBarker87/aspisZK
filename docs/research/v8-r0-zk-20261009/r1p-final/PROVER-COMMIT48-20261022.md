# Part 48: shipped simulator binding and payload image

**Target not yet established.** Work in progress on
`codex/cx-prover-commit48-20261022`, based on `26b922be6`.

D164 scope: shipped per-iteration Kani bindings, Lean induction over the owned
loops, then the complete native simulator payload byte image. No Aeneas on
shipped code. No FSExperiments conversion, joins or endpoint changes.

## Stage 1: native evaluator iteration binding

The per-call abstraction records operation tags and every operand, and feeds
arbitrary symbolic results back to both sides at corresponding calls. Equality
of the complete call trace and result establishes a parametric control-flow
binding; it does not prove an arithmetic callee contract. Part 47's separately
checked release arithmetic is reused only at its exact pinned source bodies.
The harness must cover the full 1024/512 array shapes and arbitrary legal
iteration indices; short whole-loop fixtures do not replace this obligation.

## Endpoint before/after

`../../100bit-spend-path-20261013/evidence/prover-commit48-20261022/endpoint/`
contains verbatim complete before/after snapshots, copied from part 47.
They are unchanged. The deployed theorem still requires
`RustProverRefinement`; the D159 L1 obligations remain open.

## Validation and trust

Only attempts J9900–J9999 are allocated to this job. Host compile receipts
will record target, source SHA, dependency fingerprint, exit, wall, peak RSS,
swap, source revision and every printed axiom. Host jobs use MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and the requested linker flags.
No shipped source has changed. The current S4 ELF pins apply to any later
shipped change. No wallet keys, funds, push or merge are involved.

Stage-1 results: `ProverCommitNativePair48.range_finite` / `range_owner`
compose every pair transition, including error/divergence, into the extracted
part-47 owner. `ProverCommitNativeEval48.run_owner`, `raw_value` and `bytes`
compose the nine basis stages, 512 pair steps, normalization and exact cell
image. These are P6 **evaluator denotation** theorems; the native simulator's
coefficient/tape/caller binding is still open. They are not renamed complete
simulator theorems.

Kani `basis_fill_iteration` passes on arbitrary full 512-cell arrays and every
legal `width,j` (84.548 s, 2119456 KiB RSS, zero swaps).
`basis_stage_iteration` passes (0.437 s, 139300 KiB RSS, zero swaps).
`pair_iteration`, using an arbitrary current iterator cursor and the full
1024/512 arrays, passes (14.261 s, 717272 KiB RSS, zero swaps).
All compare complete callee traces and returned state with universal symbolic
callee results; no arithmetic law is inferred from those stubs.

Failed drafts: pair v1 has an insufficient unwind bound in its test-input
`array.map` (20.502 s, no verified result). v2 times out at 180 s while replaying
that construction. v3 removes the map via a transparent representation but
still replays the iterator prefix; it is stopped without a verdict. The
replacement v4 starts at the current cursor under the explicit pure std
semantics below. No memory cap increase or unchanged retry is used.
`basis-stage-v1` is a reservation refusal before any command, not a compile.
J9900 fails on pair-pattern eta conversion; J9901 fixes it. J9901–J9903 pass,
with only standard axioms (J9903's first two theorems are axiom-free).

D157 fields added, in `ProverCommitIteratorStd48.TrustedStd`:
`slice_chunks_exact` (complete forward chunks, remainder omitted) and
`iterator_zip` (forward lockstep traversal until either input is exhausted).
Call site: `crates/aspis-core/src/r0/encoder.rs`, `eval_pair`'s
`q.chunks_exact(2).zip(basis)`. The fields concern only documented pure std
semantics, and have a proved mathematical consistency instance. They do not
assert arithmetic correctness, callback success, allocation totality,
simulator equality, or privacy. The iterator model and its count theorem
are separate from the kernel-checked evaluator induction; the remaining
source/P6 composition is stated explicitly rather than hidden as an axiom.

## Stage 2: aggregate y1 and full-width arithmetic

J9905 proves `ProverCommitY1Aggregate48.every_lane`: all 29 normalized native
evaluator-denotation calls succeed, in order, with their canonical exact
values, and the concatenated 928 bytes equal the corresponding model list.
It uses symbolic list induction and pointwise byte congruence. This replaces
the part-47 abandoned aggregation without recurrence expansion or a larger
resource limit. J9904's only failure is a final natural-number scalar notation
conversion in the byte-count lemma; it supplies no accepted theorem.

The following opening fields use arbitrary full WideExact challenges, so the
subfield-only arithmetic of part 47 is insufficient for them. J9907 proves
canonical QM31 operations and raw multiplication by the tower constant;
J9909 gives its exact decoded value; J9910 proves actual release full-width
WideExact add/mul preserve canonicality and have the exact tower value.
`ProverCommitWideOps48.mul_exact` has no checked-success, high-half-zero,
source-success, or callee-equality premise. The checked/release relation is
reused only after the checked canonical result has been established.
These close arithmetic obligations, not the semantic/interpolation caller
or complete simulator output equality. J9906 is a redundant-tactic draft;
J9908 is a rejected ambiguous-carrier draft. Their original diagnostics and
nonaccepted axiom output remain in the receipts.

J9911 proves the full canonical source limb tuple has the exact full-width
32-byte image and decoding. The actual native serializer also passes Kani on
arbitrary canonical low and high coordinates (2.674 s, 294936 KiB RSS, zero
swaps). Kani also checks the raw-M31 trait embedding chain agrees with the
semantic column lift followed by `from_qm31` (0.461 s, 158976 KiB RSS, zero
swaps). The copied field files are byte-identical to their current shipped
sources; `pins/wide-body-inputs.json` records both complete files and the
scalar-trait source pin.

## Stage 3: opening coefficient mix and fold owners

The new counter owners in `opening-owner/lib.rs` translate successfully.
Only those owned counters go through Charon/Aeneas; no shipped loop is
extracted. Their reused arithmetic declaration bodies are compared byte for
byte by `harness/bind-opening.py` before the new extracted owner definitions
are installed as `AspisR1ProducerRelease47.Opening48` (J9912).

The actual opening's coefficient-fold expression passes its arbitrary-lane
and arbitrary-coefficient-index Kani transition (5.381 s, 387972 KiB RSS,
zero swaps). The source primal fold-cell expression passes its complete
callee-trace gate (0.872 s, 167704 KiB RSS, zero swaps).
J9913 proves the **entire 29-lane coefficient mix**, with full-width
canonical inputs and exact decoded weighted sum. This is not a theorem that
the source gamma-power producer or source coefficient arrays have already
been identified with the full model trace. Those producer bindings remain
explicit work, as do the fold-array value induction and remaining semantic
and opening fields.
