# Natural-coordinate chord projection

Research continuation from `3a0b144dee108041320a23850ab4478444a74745`.
This leaf constructs the total coefficient projection required by the
[causal row game](causal-row-continuation.md). It changes no protocol,
transcript, verifier, proof bytes or production code.

The generic conversion/prefix core and its selected chord specialization are
kernel-checked. Both focused targets passed on their first run.

## Which operator the source uses

The natural circle representation is

```
Q(x,y) = A(x) + y*B(x)
A = sum_j q[2j]*phi_j, B = sum_j q[2j+1]*phi_j
phi_j = product_{bit in j} T_(2^bit).
```

For the chord `a+b*x+c*y`, full multiplication on the circle gives

```
Af = a*A+b*X*A+c*(B-X^2*B)
Bf = c*A+a*B+b*X*B.
```

The resulting pair has degree at most 513, so each half needs 514 natural
coordinates. `chord_link.rs::forward` computes those 1028 coordinates;
`inactive_row_binding.rs` zero-pads the 1024-coordinate original covector
before applying its transpose. The corresponding primal operator is
therefore **convert the full pair to natural coefficients, then retain the
first 512 coordinates in each half**. It is defined on every quotient,
including invalid images.

Monomial truncation is not this total operator. Already at width 2, `Q=x`
and chord `x` produce `x^2=(phi_2+1)/2`: natural prefix projection retains
`1/2`, while discarding monomial degrees at least 2 retains zero. Consequently
one cannot use monomial truncation for the ordinary prior on invalid-image
branches, even though both projections preserve a polynomial already inside
the original degree cap.

## Constructed mathematical interface

[NaturalProjectionCore.lean](experiments/NaturalProjectionCore.lean) defines
the extended natural coefficients literally as

```
monomialToNatural K m * vector(polynomial.coeff[0..m)).
```

The maintained `CircleNaturalBasis` proof derives nonsingularity of this
matrix from its triangular degrees and nonzero diagonal; no rank assumption
is introduced. The new core proves the conversion evaluates to the entire
polynomial whenever its degree fits the width, and proves the prefix is
adjoint to zero-padding the original covector. At width 514 the full chord
pair always fits, independently of image validity.

The [selected leaf](experiments/NaturalChordProjection.lean) then proves that,
for an image-valid quotient, the literal conditions
`q[1023]=0` and `b*q[1022]-c*q[1021]=0`, with `(b,c)` nonzero, imply the pair's
degree cap 511 by `NaturalChordImage.selected_image_iff`. The projected pair
therefore represents the full chord product, not an assumed reconstruction.
Its evaluation is multiplication by the chord **on the circle**.

The circle premise is essential: with `Q=y`, chord `y`, and off-circle
`x=y=1`, coefficient reconstruction evaluates to `1-x^2=0`, but literal
pointwise multiplication is `y^2=1`. Actual stored source points are on the
circle; this is a falsifier for omitting the premise from a generic bridge,
not a source acceptance attack.

## Reused V7 and earlier prerequisites

| Maintained theorem | Exact reuse and boundary |
|---|---|
| `CircleNaturalBasis.naturalCoeff_mul_monomialToNatural` | Canonical inverse matrix with proved nonsingularity at every width |
| `V5FriConcreteEncoderApplicability.naturalCoefficientPolynomial_complete` and `_injective` | Existence/uniqueness of natural coefficients; no assumed successful decoder or arbitrary evaluation-matrix rank |
| `V5FriInitialCircleEncoderIdentity.initialP0/initialP1` | The same even/odd natural coefficient convention; the old file's log19 domain must not replace the selected log20 domain |
| `Pool/V7C1ConcreteProjectionBinding.exactInitialEncoder` | Actual mathematical stored-log20 evaluator of the two polynomial halves, with the proved 1024-symbol overlap cap |
| `K1/V7Tag73ExactOneFoldEncoderBinding.exactInitialEncoder_eq_circleLift` | Literal log20 four-slot lift and selected final-line evaluator; final overlap cap 255 |
| `V7ExactOneFoldDomains` | Stored bit-reversed points and four-slot coordinate signs; their circle-group subtype supplies the circle equation |

The last three are useful source-shaped mathematical interfaces, not a
claim that this continuation translates the Rust FFT, sparse carry kernel,
optimized contraction, parser or immutable authenticated-opening access.
`exactOneFoldAlgebraBinding` also retains explicit encoder/inverse-table
equalities; its packaging does not discharge those source premises.

## Scope of the advancement

This removes the ambiguity between a coefficient-space reconstruction and
the actual circle chord multiplication for the represented image-valid
class, while defining the correct total natural projection outside it.
The received oracle is not assumed globally polynomial. Its agreement with
the reconstructed polynomial must still be obtained in the coupled causal
experiment before using a supported-reference theorem.

The full interleaved linear-map packaging, literal sparse-carry/optimized
transpose refinement, source-domain instantiation, and arbitrary accepted
recovery coverage must be tracked separately. Neither this deterministic
interface nor the existing near-gamma result bounds the entire event
`acceptance AND failed checked-witness extraction`.

No security error is added or removed. The 40,282-byte body and all measured
CU/prover figures remain unchanged; no performance suite was rerun.

## Focused reproduction

Run from this research directory:

```
bash experiments/run_natural_chord_projection.sh NaturalProjectionCore experiments/natural-projection-core-v1.log
```

The core passed on its first focused run: exit 0, 3.17 seconds, peak RSS
5,650,923,520 bytes, zero swaps. Five audited theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. There are no `sorry` or new axioms.
Its source SHA-256 is
`42bb9c9139a679fbe6c71a0573d9e6c08ab9da740c0613c7b9275f84aaefdae6`;
the olean SHA-256 is
`e86e3aee4d8faf0cfd866211c8e033db597f727ef094b8484c715be877eabd15`.

The dependent selected target also passed first time:

```
bash experiments/run_natural_chord_projection.sh NaturalChordProjection experiments/natural-chord-projection-v1.log
```

Exit 0, 3.36 seconds, peak RSS 5,640,585,216 bytes, zero swaps, four standard
axiom audits. Source SHA-256:
`8176b1fbd925a523602b5b53ee529547db6322bdaff84da8527404284619f4be`;
olean SHA-256:
`a2c296177afcb79998c563a346474ca1a9a01116ce2f324f4bbeb66cec519386`.
The unchanged runner SHA-256 for both commands is
`bc1823f0beded90f1ea23507bdd0f212da0fa7f3028bee1544804c0a9bfd4250`.

The parent separately isolated/repaired a concrete-specialization resource
failure in the image dependency, whose final export is pinned in the
dependent log. Neither of this leaf's successful runs silently reused a
stale image olean. All import source/olean hashes stayed unchanged during
both focused runs. Concurrent parent/other-agent research files were
preserved; none of this agent's work changes main.

The runner pins the research source revision, mathlib revision, the complete
Aspis import closure against the cache's source, and records source/olean
hashes before and after the focused leaf. It uses `-M7000`, an independent
7-GiB aggregate-RSS stop, `/usr/bin/time -l`, and named axiom audits.
