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

## Stage 3: semantic guard and final-round composition

J10714 proves the actual intended semantic model function's degree bound,
original-round decomposition, initial/chain/terminal guards, and terminal read
from refPayload+L. J10716 identifies every shifted model round polynomial
with refPayload+L after shift, and proves its boundary and terminal laws.
J10718 composes the source partial sums, interpolation and actual inverse/shift
producers into the entire round-9 polynomial of that model payload. This
retains explicit per-oracle-call correctness, challenge prefix, non-half, and
the two source terminal-input images. It does not promote those input cuts
to a whole native semantic implementation theorem.

J10720 proves the canonical source boundary comparison and composes the
actual source polynomial evaluator with each next boundary guard. The
polynomial images and initial running input image remain caller obligations.
J10722 reassembles all eight independent WideExact component equalities
into complete ordered list equality and connects that list to the extracted
strided collector. Native Kani results remain external evidence, not axioms.

| Attempt | Exact module | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| J10714 | R1Z.ProverCommitSemanticModel55 | 0 | 2.89 | 3613976 | 0 |
| J10716 | R1Z.ProverCommitSemanticRounds55 | 0 | 2.80 | 4168316 | 0 |
| J10718 | R1Z.ProverCommitSemanticFinal55 | 0 | 2.24 | 4183196 | 0 |
| J10720 | R1Z.ProverCommitSemanticGuards55 | 0 | 2.30 | 4149812 | 0 |
| J10722 | R1Z.ProverCommitCollection55 | 0 | 1.77 | 4100584 | 0 |

Every printed accepted axiom is standard only. J10712/13 are type/transparency
drafts; the latter hit the default recursion limit on a payload projection.
J10715 repeats a rewrite already applied to both occurrences. J10717 hits the
unchanged heartbeat limit under a polynomial `change`; J10718 uses a named
identity. J10719 uses a reserved identifier and lacks local equality
decidability. J10721 needs zero-add normalization before list transitivity.
All rejected snapshots/diagnostics are retained. No Lean limit is raised.

All eight WideExact-256 selected-word checks now pass with complete native
allocation/collection, arbitrary raw input words and arbitrary output index.
The word receipts are e-split-256-word0-v3 through word7-v3, all exit 0, zero
swap, with peaks approximately 4.13 GiB. This completes the split collection
checks for every actual recursive length/type used by the caller.

Native constructor-order checks at lengths 4,9,10, semantic challenge arrays,
and canonical M31/QM31 projection round trips also pass. The constructor
v3 diagnostic is an intrinsic memcmp unwinding failure; v4 changes the
comparison to a selected component and covers its remaining tiny comparisons.
An earlier reservation hold launches no compiler. All native scopes stay
6G/8G/zero-swap/64 tasks.

The full native CM31 arithmetic-step comparison times out after 180.568 s
(169536 KiB RSS, zero swap). A different release-flags preflight is rejected
by Kani because it requires overflow checks; no analysis runs under that
configuration and it establishes nothing. The symbolic square/power proofs
remain valid, while the native arithmetic-step gate is not claimed proved.
The channel-0 v3 failure is confined to generating 1024 arbitrary input cells:
its 260 unwind bound covers the collector but not that input constructor.
The revised harness explicitly covers that 1024-step setup; memory caps stay
fixed. No failed native input is replayed unchanged.
