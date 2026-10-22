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
