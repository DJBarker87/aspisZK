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


## Stage 2: guarded values, interpolation, prefix and optimized power

J10704 proves complete canonical guarded evaluation by composing the guard
equivalence with the retained generic evaluator. J10705 derives all owned
partial sums and the standard round polynomial from the per-call oracle
results at actual source sample points; no polynomial or sample-sum array
image is a premise. Per-oracle result correctness and the prefix relation
remain explicit. J10710 derives the semantic index relation and source
sample/tail/next-alpha prefix preservation. Initial prefix is unconditional;
the source update reads exactly semantic position 15+r. These local results
do not yet bind the entire native round driver or its semantic oracle.

J10706 checks an exact recursive owner of CM31 power using the native bit
condition, optimized square, and right shift. J10711 proves success,
canonicality and acc*base^exp for every u64 exponent. Unlike the previous
multiply-square owner, this owner calls the actual optimized CM31.square.
Every reused extraction declaration is byte-identical, recorded in
encoder-native-nodes-callee-binding.json. Native while-loop composition
remains a distinct step. J10707/09 are failed shift-transparency/let-rewrite
drafts; J10708 is a failed platform-dependent usize addition draft. The
replacements use a concrete one-bit shift and the proved bounded addition.
All accepted printed axioms are standard only.

| Attempt | Exact module | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| J10704 | R1Z.ProverCommitEncoderGuardValue55 | 0 | 1.72 | 4100224 | 0 |
| J10705 | R1Z.ProverCommitSemanticInterpolation55 | 0 | 2.28 | 4131836 | 0 |
| J10706 | AspisR1ProducerRelease47.EncoderNativeNodes55 | 0 | 1.30 | 2635072 | 0 |
| J10710 | R1Z.ProverCommitChallengePrefix55 | 0 | 1.97 | 4125740 | 0 |
| J10711 | R1Z.ProverCommitEncoderNativePower55 | 0 | 2.51 | 4116108 | 0 |

The optimized power extraction exits 0/0 (1.133/0.313 s,
213520/61776 KiB RSS, zero swap). The reservation preflight waited before
launching when another 8-GiB scope would exceed the 55-GiB reservation.

All native smaller even/odd collections now pass at lengths 2,4,8,16,32,64,
128 for M31, QM31 and WideExact. No allocator, Vec, iterator or callee is
stubbed. The largest smaller check, WideExact-128, exits 0 in 177.963 s at
5575076 KiB RSS with zero swap. Exact commands, scope limits, source revision,
hashes, snapshots, wall/RSS/swap and raw logs are in the named receipts.

The full-record WideExact-256 check was stopped during memory growth at
6456720 KiB (71.837 s), exit 1, zero swap; no cap was raised and it was not
retried unchanged. The replacement verifies output words separately, while
retaining the complete allocation and both native collect paths. Word 0
passes in 88.255 s at 4333640 KiB, exit 0, zero swap. Remaining words are
being checked independently; no complete WideExact-256 claim is made yet.
