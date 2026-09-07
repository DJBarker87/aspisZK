# Continuation verdict: chord closure survives; the 100-bit claim does not yet follow

Date: 2026-09-07. User explicitly accepted **40,282 bytes** in this continuation.
This removes the canonical q22 model's byte objection; it does not approve a
larger unspecified body or change the security/CU requirements. Historical
40,000-byte and 40,960-byte categories remain in the original harness.

## Exact source and scope

Research base: 77cb6ea900d24b03a536a0e0649e3fc6d0b1a79d, selected source inherited
from 4c91f97ac6576201f90d41c2a575e54c026e3796. Inspected separate V8 branch
d9962e0d265c99172420d47566c96469c83ef7bd without editing it. Concurrent main
b053663d6c4fc7e991ef08ca568f68b81d25311c has unrelated dirty formal/transcript
work, left untouched. This is not a certification of that newer main revision.

Source anchors:

- `crates/aspis-core/src/sumcheck.rs::WeightAccumulator::add_circle_tensor`:
  factors y, x, pi(x), ..., pi^8(x), reversed for stored tensor order.
- `crates/aspis-prover/src/circle_candidate.rs::CircleEncoder::encode_c1_basis_value`:
  exact butterfly-path matrix, with y in bit zero and successive line factors.
- `crates/aspis-core/src/circle_fri.rs::normalized_circle_to_line_arity4_prepared_with_square`:
  slots (x,y), (x,-y), (-x,-y), (-x,y); circle alpha then line alpha squared.
- `crates/aspis-prover/src/v6_onefold_prover.rs`, combined message through
  final256 (approximately lines 1497–1592): relation and codeword both fold the
  **original** combined message, not a chord quotient.
- Separate V8 `v8_deep.rs::two_point_chord_zerofier` and
  `v8_two_point_circle_quotient_reference`: the precise affine chord/interpolant.
- Separate V8 `K1/V8A100PreGammaTupleBinding.lean`:
  `ExactCompilerPreGammaTupleObligation`, `restored_k14_branches_use_one_fixed_tuple`.

## Universal algebraic derivation (not a Lean proof)

Work in K=QM31, characteristic odd, with the production element i satisfying
i²=-1. The tensor factors x, pi(x), ..., pi^8(x) have degrees 1,2,...,256 and
nonzero leading coefficients. Their subset products have distinct degrees
0,...,511, hence form a triangular basis of all polynomials of degree <=511.
The released space is therefore exactly

    W = { A(x) + y B(x) : deg A <= 511, deg B <= 511 }, x²+y²=1.

Let z=x+i*y. Then z is nonzero, z^-1=x-i*y, x=(z+z^-1)/2 and
y=(z-z^-1)/(2i). Thus W has Laurent support [-512,512] and the coefficients
at +512 and -512 sum to zero. Conversely these conditions describe W:
the Laurent space with that single constraint has dimension 1024, and the
1024 independent original basis vectors belong to it.

For two distinct finite circle points, their nonzero chord is
L=a+b*x+c*y=l_- z^-1+a+l_+ z. Both l_- and l_+ are nonzero. Otherwise zL
would have at most one distinct nonzero root, contrary to containing the two
distinct points. The chord cannot vanish identically because b=c=0 would make
the points equal. Its two roots are exactly those points; legal OOD points
therefore cannot make a denominator vanish on the base evaluation domain.

The source affine interpolant I uses x if the two x coordinates differ,
otherwise y. It is in W, has Laurent support [-1,1], and matches both values.
For any honest f in W, z^512(f-I) is divisible by zL, a quadratic with these
two distinct roots. The quotient has degree <=1022. Consequently

    Q=(f-I)/L has Laurent support [-511,511],
    Q=A_Q(x)+y B_Q(x), deg A_Q <=511, deg B_Q <=510.

This is **inside W**, not a larger code. The source normalized four-point fold
is the polynomial

    A_even(x²) + alpha B_even(x²)
      + alpha² A_odd(x²) + alpha³ B_odd(x²),

where A(x)=A_even(x²)+x A_odd(x²), and similarly for B. Its degree in x² is
at most 255. Since pi(x)=2x²-1 is an invertible affine change of variable,
it fits the selected 256-dimensional final line tensor. No larger final
disclosure is forced by honest chord division. This resolves the degree/image
question algebraically, not the complete authenticated source refinement.

## Reverse membership and relation: what a verifier still owes

The image of f -> (f-I_f)/L has dimension **1022**, not 1024: its kernel is
the two-dimensional interpolation space span{1,h}. A generic Q in W is not
automatically in that image. The exact image consists of Laurent support
[-511,511] with the additional constraint

    l_+ * Q[511] + l_- * Q[-511] = 0.

That constraint prevents an x^512 term in LQ+I. For example Q=z^511 is in W
but violates it because l_+ !=0. This is a counterexample to the proposed
shortcut "any low-degree quotient reconstructs an original message", **not**
an attack on an implemented V8 verifier. A complete decoder/link proof may
derive the constraint from authenticated agreement and distance rather than
adding a direct verifier check; that derivation is currently missing too.

Blindly retaining V7's relation check is also invalid. Take f=h, where h is
the interpolation coordinate: I=f and Q=0. An arbitrary original linear
claim about f is not the same claim about Q. To preserve the semantic link,
write f=M_L Q+I on the constrained image and transform each relation
functional w to M_L^T w, subtracting w(I) from its claimed value. One must
prove that the implemented coefficient ordering, membership conditions and
terminal evaluation perform this identity. Merely evaluating Q correctly at
the authenticated query leaves does not implement that relation transformation.

These are linear constraints and need not inherently add proof bytes: known
zero claims can potentially join the relation batch. But challenge order,
batching root counts, weight-evaluation CU and full-view hiding must all be
recomputed. **No zero-CU or zero-security-loss substitution is justified.**
The 40,282-byte census remains a layout model, not a complete-protocol census.

## Fixed-tuple theorem: existence is not uniqueness

The inspected Lean theorem proves equality of components for two supplied
coherent K1.4 branches whose component evaluations match the pre-gamma prefix.
Its missing structure supplies a K1.4 family, refinement to the actual K1.3
compiler family, and prefix replay. It does not construct coherent extractions
from arbitrary accepted/restored continuations. If no coherent branch exists,
its pairwise uniqueness statement can be vacuously true.

Thus it cannot alone replace the old correlated-agreement/coherence error by
28/(|K|-1). Constructing its provider by assuming the old K1.4 success event
would retain the old error, not eliminate it. This is a logical limitation of
the claimed implication, not a proof that a new DEEP extraction argument is
impossible. A new existence/recovery theorem for the actual quotient and the
authenticated heterogeneous/adaptive oracles must precede a 100-bit assertion.

## Executed evidence

`experiments/chord.rs` imports the pinned production field and circle map.
It uses the equivalent monomial basis of W, not an FFT or a full prover.
For every one of its 1024 basis vectors and two legal OOD pairs (including
equal-x/opposite-y), it computes exact Laurent division, checks zero remainder,
reconstructs every numerator coefficient, and checks the image constraint.
For the two degree-512 input examples it also reconstructs A_Q,B_Q through
Chebyshev recurrences and checks the literal nested fold at 32 points against
a degree-255 polynomial. The copied fold identity uses K coordinates; this is
not an execution of the complete production fold module or its domain indexing.

Command, from the worktree root:

```sh
rustc --edition=2021 -O docs/research/v8-no-work-100-20260907/experiments/chord.rs -o /tmp/aspis-v8-chord
/usr/bin/time -l /tmp/aspis-v8-chord
```

Final changed-source run: exit 0, 0.58 s wall, 0.18 s user, 2,867,200 bytes
maximum RSS, zero swaps, zero block input/output operations. Apple M3/macOS,
Rust 1.93.0. Compilation is excluded from the timed execution. No witness,
network, full proof generation or SBF execution. Earlier narrower run passed
2048 basis divisions; rerun added the Chebyshev/fold checks. These are exact
finite tests, not probability estimates, universal adaptive ZK or formal proofs.

## Firm decision under the revised byte allowance

**No investigated implementation currently justifies the requested 100-bit,
no-CU-regression claim.** Accepting 40,282 bytes solves only the canonical q22
layout objection. The honest chord degree is not the blocker; the authenticated
extraction/relation transformation and adaptive hiding are. It is not defensible
to report the conditional 104.27-bit model as achieved security.

Keep canonical QM31 q22 as the primary research direction: it preserves field
kernels, avoids packed fixed parsing, and now meets the accepted modeled size.
Do not implement a large prover/SBF build on the strength of tuple uniqueness.
The single decisive next gate is a source-bound **coherent extraction existence
and relation-link construction for the virtual chord oracle**, including the
two image constraints (or their derivation) and cached/advance continuations.
Stop this claimed 100-bit argument if it still needs the old ~75-bit coherence
error. Recompute the complete error sum if it incurs a new list/selection loss.

Selective p^8 remains the fallback, not a validated alternative: it avoids
relying on this particular numerical improvement but still requires the field
descent, widened-view hiding and circle-list theorem, and has much worse dense
memory. No measured CU relaxation can be named. Further raw arithmetic or field
microbenchmarks cannot decide these missing cryptographic statements.
