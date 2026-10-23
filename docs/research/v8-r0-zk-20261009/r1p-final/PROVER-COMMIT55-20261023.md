# Part 55: native collection and caller bindings

Target not yet established. Branch `codex/cx-prover-commit55-20261023`.
Only J10700–J10799 are authorized. No shipped source changed.

## Endpoint before

The full verbatim deployed endpoint is retained in
`../../100bit-spend-path-20261013/evidence/prover-commit55-20261023/endpoint/before.lean.txt`.
Its RustProverRefinement premise remains explicit.

## Stages

Stage 1 establishes the extracted native length guard equals the retained
height guard for every input list of length 2^h, h≤8, every trait record,
node array and starting depth. The collector output lengths are derived;
no canonicality or arithmetic-success hypothesis is needed for equivalence.
The added proof fuel is unreachable on all branches covered by this theorem.
This is not yet a native-recursion execution theorem.

J10700 checks the exact new extraction (exit 0, 1.72 s, 2636676 KiB RSS,
zero swap). J10703 proves `R1Z.ProverCommitEncoderGuard55.equivalent`
(exit 0, 2.57 s, 4122004 KiB RSS, zero swap), with printed axioms
[propext, Classical.choice, Quot.sound]. J10701/02 are retained failed drafts:
Boolean simplification and the Vec.deref coercion required explicit handling.
No limit was raised. Exact revision, source hash, dependencies, command and
full diagnostics are in lean/J10700–10703.json.

Charon/Aeneas accept the structurally recursive guarded owner (1.267/0.458 s,
215612/64944 KiB, zero swap). Every reused collector declaration is byte-equal
and recorded in encoder-guard-callee-binding.json. The native length guard is
retained; the fuel assertion is an explicit proof instrumentation boundary.

Complete actual Rust `collect` expressions, including allocation, both
iterator paths and output lengths, are checked at length 256 for arbitrary
raw M31 and QM31 cells. An arbitrary selected output index covers every cell.
No iterator, allocator, Vec or field method is stubbed. M31 passes in 22.095 s
(1349988 KiB); QM31 passes in 128.338 s (4022108 KiB), both exit 0, zero swap.
The exact receipts are m-split-256-v1 and q-split-256-v2. RUSTFLAGS supplies
opt-level=3 despite Kani's Cargo dev-profile banner. The scope is 6G/8G,
zero swap, 64 tasks. These are compiler-pinned native collection checks;
smaller recursive lengths, WideExact and caller composition are still open.

The source revision is the task base in revision.txt (the first native input
receipts abbreviate it as 341584654f). Exact source snapshots and hashes are
retained. No shared object was overwritten; cache links are read-only.

