# Resource reset, not another FFT tuning round

## Why this happened

The old efficient implementation represented a verifier-derived functional
compactly and evaluated its final contraction without materializing its full
covector. The privacy repair changed the coordinate transform and G
functional. Research implementations used a dense, transparently correct
reference route. That route then reached SBF before a viable compact
algorithm and resource gate existed. The Vandermonde choice makes an easy
mixing/invertibility argument but an expensive verifier functional; solving
the mathematical conditioning problem did not solve the on-chain cost.
The second complete reference verifier and an internal opening reference
also remain in diagnostic code. Those are different costs and must not be
confused with the already-too-expensive primary pass.

This package does not blame Lean: off-chain proofs do not consume on-chain
CU. It changes the operation that needs proving, while retaining mandatory
source and full-view verification.

## Changes and their boundaries

| Change | Expected mechanism | Security / evidence boundary |
|---|---|---|
| Sparse G on (Tg)[128+3i] | Delete tree/FFT/full weight transforms; 271 gather/scatter coordinates | NEW profile; finite image checks passed, actual source and universal privacy open |
| Share A/E/H contraction | Compute common ordinary functional once | Same-profile arbitrary-vector algebra; retain separate channels |
| Optional 163-support T | 316 fewer changed-coordinate weights than old479 construction | SECOND new profile; H1/G screening passed, source certificates must change |
| Diagnostic/primary split | Stop executing independent reference twice on-chain | Only after showing each omitted assertion duplicates retained checks |
| Old 1024 FFT/carry patch | Already integrated into R43 | Do not re-propose as unfinished |

The sparse terminal's386 multiplication count excludes coefficient generation,
geometry, all ordinary work, semantic verification, authentication, query
injection, final folding and source execution overhead. Do not convert it to
CU with an invented universal multiplier. The only valid end-to-end claim is
an accepted complete SBF measurement under the specified source/profile.

## Benchmark staging

1. Keep preferred R43 artifacts and measure only changed candidates.
2. Build sparse G first with unchanged T to isolate effects. New transcript
   means new fixtures; compare same public statements and retain source hashes.
3. Instrument and measure; fail fast on source privacy/correctness loss.
4. Try163-support T separately, then common ordinary-block reuse. Reuse actual
   tensor/fused/grouped kernels; do not write another dense reference as the
   optimized verifier.
5. Keep host/differential reference checks and production checks distinct.
6. Enforce both stack-frame and heap gates, not compiler exit0 alone.
7. Require successful primary, successful complete entry point and completed
   negative rejections. Explicitly include account handling/settlement before
   claiming final transaction viability.

## Memory schedule

The initial Rust draft's271-entry return value is host-oriented. Use output
slices in SBF. A reused area of399 QM31 fields (271 coin coefficients plus
128 group-pair values) is6384bytes of heap storage, not a stack object. Geometry
and temporary four-element values stay bounded. Share this storage with
consumed proof/fold buffers only after proving lifetime and unread-element
preservation. The optional163-index correction should reuse bounded storage;
freeze indices and cycle schedules in readonly data rather than heap Vecs.

Do not change allocation failure from visible error to unchecked memory
access. Do not implement hash-dependent/secret-dependent path skipping to
hit a benchmark. Public fixed index/sparsity schedules suffice here.

## Rejected direction

The bit-affine permutation improves tensor structure spectacularly, but its
modeled H1 constraint map loses23 dimensions. It therefore fails this
packet's screen even though raw repair, G rank, inverse and tensor tests
pass. This is precisely why optimizing only G or honest proof acceptance is
not an adequate privacy review.
