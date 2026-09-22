# R20: exact execution changes, not a new proof protocol

## 1. Fold beta into gamma coefficients, once

Let S=sum(j=0..28) gamma^j m_j and G=gamma^27 m_27.
The source uses lerp(S-G,G,beta), not two independently computed quotient
channels. Its value is

    sum(j != 27) (1-beta) gamma^j m_j + beta gamma^27 m_27.

Prepare these 29 coefficients once. Reuse the source's partial-reduction
mixed-width C1 dot and prepared C2 helper dot, with the new coefficients.
Do not pass the altered coefficients into an API whose type promises they
are literally successive powers of gamma. Define a coefficient-only prepared
view, or reuse only the parts whose arbitrary-coefficient contract is tested.

Both C1 and C2 must be fully decoded before any result is returned. In
particular beta=0 does NOT license omitting G validation; beta=1 does NOT
license omitting C1/H1/D validation. Keep leaf hashes on the original packed
bytes and do not change authentication or pole checks. This is byte-compatible
with the existing proof and introduces no new public observation or challenge.

The current lerp costs one full field multiplication, not two. A conservative
source-level opportunity is the extra G multiplication plus lerp on each of
88 slots, against up to 29 once-per-proof coefficient products: 147 logical
QM31 products before considering compiler reuse. Do NOT convert that number
into CU without SBF measurement. Hoist the two mixed interpolant coefficients
out of the query-record loop too, unless optimized emission already does so.

## 2. Whole-dot reconstruction

QM31 is CM31[u]/(u²-(2+i)); CM31 has i²=-1. The 9 Karatsuba product channels
are M31-linear before their final reconstruction into four canonical limbs.
Therefore one may accumulate the channels across an entire dot product,
then reconstruct once. Existing small-arity helpers already exploit this for
2/3/4 products. The R20 candidate extends it beyond those groups.

For canonical factors at most P-1, four products are at most 4(P-1)²<2^64.
For such a chunk t, one Mersenne fold f(t)=(t & P)+(t>>31) is congruent to t
and less than 5P. For at most 4096 terms there are at most 1024 chunks, so
all accumulated partial representatives are below 5120P<2^44. A full
canonical reduction at the end is therefore safe. The general full-u64
reducer is retained; the old incorrect '<2^62 is enough' shortcut is NOT used.

A length-27 dot needs 9 final canonical reductions and at most 7*9 partial
folds, versus 27*9 canonical product reductions in a naive scalar loop.
Against an already batched implementation the gain is smaller. Include
operand decomposition, reads, temporary storage and reconstruction in the
actual benchmark. These counts are NOT an SBF speedup theorem.

Avoid an array of 64 accumulators on the SBF stack. Process each sparse group
sequentially with two small accumulators, depositing canonical normal/carry
values into the existing 128-field caller-owned workspace. Handle zero and
at-most-four-term groups separately so that sparse carries do not pay for
an unnecessary full large-dot setup.

## 3. Shared semantic power basis

For the source compact semantic polynomial with sent coefficients c0,c2,...,c27,

    p(x) = claim*x + c0*(1-2x) + sum(d=2..27) c_d*(x^d-x).

The parent source's G coin functional uses exactly these 27 basis values at
each semantic challenge, multiplied by a fixed power of one-half. Thus a
semantic evaluator can retain that basis for the later G calculation; it need
not form it again. A source implementation must keep one correctly indexed
cache for every round and bind its entries to that round's actual challenge.
The test includes a stale-cache negative.

This is a sharing opportunity, not an automatic product-count reduction:
generating a basis for a batched dot costs work that Horner avoids. Compare
(a) current block-Horner + later G basis, (b) basis+whole-dot with retained
cache, and (c) shared baby/giant powers. Do not count the old G power work as
saved while hiding its replacement in semantic verification.

Ten 27-field caches use 4320 bytes. They must be in caller-owned heap storage,
not returned as a 4320-byte SBF stack array. An alternative retains small
power blocks and trades some recomputation for storage. No mask randomness
is cached or resampled: all these values are public functions of challenges.

## 4. Semantic digest residuals

For any fixed K-linear packing operator L and events with the SAME opened
segment and destination lane group,

    sum_l h_l L(opened-expected_l)
      = (sum_l h_l) L(opened) - sum_l h_l L(expected_l).

The inspected append path passes the same [QM31;16] opened array into
per-level routines. Aggregate by exact destination/local-selector class.
Keep each actual expected digest, domain tweak, level/carry condition and
recipient-presence rule. The small model has generic event groups: source
instantiation, including its lane offsets, has NOT run here.

For M31 expected limbs, base packing is the canonical field element with
those four limbs. Avoid making 8 extension-field differences and then
packing them for every level. Factor the opened part once per group and
use a whole dot for the expected-digest part. Pass immutable opened/frontier/
selector arrays by reference. Whether LLVM already elides a particular
by-value copy is a compiler question, not a proven cost in this packet.

## 5. Scalar transpose of the sparse G terminal

The grouped map has normal n_l, carry c_l (l<3), and high h_j. After pairing
its four outputs with final coefficients f, define H_g=h_(g mod16) f_(g/16).
Move the carry contraction to its transpose on H, giving C. Then the scalar
coefficient at code coordinate j=16g+l is

    v_j = n_l H_g + [l<3] c_l C_g.

The tested scalar algorithm evaluates each 27-coefficient zero-boundary
polynomial by Horner against v_j and scales only the ten completed round
sums. It agrees with the full independent chord adjoint, including zero/one
challenges and arbitrary final coefficients. It does NOT always use fewer
products than computing four outputs. Retain it as a differential oracle
and benchmark candidate; do not promote it on the word 'scalar'.

The current source also constructs the same abc/alpha geometry independently
inside ordinary and G terminals. Share it once where the assembled source
really has the duplicate. That is not a new transcript or mask design.

## 6. Two-lane canonical arithmetic

Pack two canonical 31-bit limbs in separate 32-bit slots of a u64. For their
sum s, canonical reduction in both slots is

    (s + (((s+ONES)>>31)&ONES)) & MASK,
    ONES=0x0000000100000001, MASK=0x7fffffff7fffffff.

Each lane sum is <=2P-2, so neither lane carries into the next slot and the
whole word does not overflow. Subtraction uses s=a+MASK-b: each lane is
nonnegative, <=2P-1, and there is no cross-lane borrow. One-bit halving uses
((a>>1)&0x3fffffff3fffffff)|((a&ONES)<<30).

The Rust draft has a private canonical type with checked construction and
operations preserving its invariant. It does NOT reinterpret arbitrary
M31(u32) instances as canonical. Validation must be at the real source
boundary, not assumed because honest tests pass. The source's existing
canonical decoder and error cases remain authoritative.

The included 16-product/6-reduction QM31 multiplier is a comparison backend,
not a claimed new discovery relative to R19's staged hybrid/lazy kernels.
Compare actual assembled files and emitted code before using it. More base
products can be faster or slower depending on reductions/register pressure;
only a measured whole-verifier A/B can select it.
