# Exact circle-GRS submodule and linear-factor message recovery

Parent revision: `6f1ebbe55fcc6fd008071329d5270aae0521cf9a`.
This is a companion to [the interpolation result](linear-factor-interpolation-review.md).
The generic linearity, selected submodule, and final actual-message
recovery composition are all kernel-checked and frozen.

## Source boundary

The actual V7/V8 numerator map is

`exactCircleGRSPolynomial m = circleNumerator (initialP0 m) (initialP1 m)`.

It is not the entire ambient degree-at-most-1024 polynomial space. The
new generic [CircleGRSLinearity](experiments/CircleGRSLinearity.lean) proves
its polynomial-level linearity symbolically. The maintained natural
coefficient map is a matrix product followed by a monomial sum. Even/odd
coefficient projections are linear. The fractional lift is a finite sum
linear in input coefficients; expansion by two is an algebra homomorphism;
the two lifted halves form the literal `circleNumerator`. No domain,
natural-basis polynomial, or 512-term lift is evaluated concretely.

[SelectedGRSSubmodule](experiments/SelectedGRSSubmodule.lean) packages this
literal map as `encoder`, with `originalCode = LinearMap.range encoder`.
Membership is exactly existence of an actual `Fin 1024 → QM31Exact`
message, not a new ambient membership assumption. Degree ≤1024 and
injectivity reuse the existing V7 exact conversion theorems unchanged.
An arbitrary coefficient tuple in the range has unique actual-message
lifts; the existence proof is mathematical, not an implemented decoder.

The checked [SelectedLinearFactorRecovery](experiments/SelectedLinearFactorRecovery.lean)
combines this actual submodule with polynomial-valued interpolation
and the root agent's checked primitive-factor regularity. For a fixed
linear-Y prime factor, a polynomial root automatically has nonzero
specialized leading coefficient. Thus the geometric good set can be
defined simply by existence of an actual original-code message rooting
the factor. Under the separately stated polynomial-in-gamma rational-root
class premise, either at most 28 good challenges exist, or a fixed
`Fin 29 → Fin 1024 → QM31Exact` tuple identifies every later polynomial
root. It also identifies each rational-root coefficient with the exact
GRS polynomial of its recovered message. This does not assert that all
retained factors belong to that class. The sparse conclusion bounds the
number of hit challenges for a fixed factor, not the probability that a
factor has the sparse property.

No support size, transcript probability, efficient factorization, sampled
extraction, source replay, authenticated opening, canonical decoding, or
payment validity is asserted by these interfaces. In particular, recovering
QM31 message components does not establish their common own support,
base-field/canonical descent, early-C1 projection, semantic validity, or
executable extractor access.

## Reused immutable sources

The runner verifies the full imported source/cache closure, with borrowed
V7 sources pinned to `26a9cd4718aae9f9de7ef1c3394fb74a229085d5` and Mathlib
to `81a5d257c8e410db227a6665ed08f64fea08e997`. Key inspected source hashes:

| Source | SHA-256 |
| --- | --- |
| V5FriInitialCircleEncoderIdentity | `2bde5263fbfae6730288883515b1689a1856ace2b428a73d6a985f256b608084` |
| V5FriConcreteEncoderApplicability | `91d8d7a2d8e1ea832459a439482aa858e970cba1608ab7652bdfce3eede632d3` |
| V5FriCircleEncoderDistance | `909dc85e736ceb7997a6f7d7d31c600531712c34015a3ab6d33beb2e66b46525` |
| V7Tag73ExactGRSConversion | `918ff7b5b1933caaf9d343c95936cb3d392d86582ec1cfd10a24161c7cdb60bc` |

## Focused evidence

NUC only, workspace `aspis-linear-factor.8SUGGL`, shared pinned
[runner](experiments/run_linear_factor_nuc.sh), MemoryHigh8GiB,
MemoryMax10GiB, SwapMax0, CPU200%, `lean -j1 -M9500`.

| Target / attempt | Exit | Wall | Peak RSS (KiB) | Swap | Status |
| --- | ---: | ---: | ---: | ---: | --- |
| CircleGRSLinearity v1 | 1 | 3.61s | 6,723,496 | 0 | Diagnostic only |
| CircleGRSLinearity v2 | 0 | 3.48s | 6,755,904 | 0 | Five standard-only axiom audits |
| SelectedGRSSubmodule v1 | 1 | 2.69s | 6,785,136 | 0 | Diagnostic only |
| SelectedGRSSubmodule v2 | 0 | 2.93s | 6,822,760 | 0 | Five standard-only axiom audits |
| SelectedLinearFactorRecovery v1 | 0 | 3.31s | 6,842,716 | 0 | Three standard-only axiom audits |

V1 has one local rewrite-order failure in fractional-lift scalar
linearity: rewriting `a • p` to `C a * p` prevented `coeff_smul` from
matching. The checked V2 repair uses the matching `coeff_C_mul` lemma.
Failed dependent axiom output containing `sorryAx` is retained only as a
diagnostic. No limits were raised and no unchanged replay was made.
The exact failed source, log and manifest use the prefix
`experiments/circle-grs-linearity-nuc-v1`.

Green generic source SHA-256:
`94ad2041deabb414e80f933ce4b4232799691827d0838134f2969134b8f10395`.
Green generic olean SHA-256:
`b5992fed5a2e093cb675ec8292230024b81aade5bf01c09b15ded8cfd6060c1e`.
Green source, log, manifest use `experiments/circle-grs-linearity-nuc-v2`.
All five audits list only `propext`, `Classical.choice`, and `Quot.sound`.

Selected v1 attempted definitional equality across the concrete QM31
linear-map specialization and the released polynomial, hitting recursion
depth 200. V2 proves the numerator-map application equality generically,
then composes it with the cached exact released equality. Range/injection
proofs transport named equalities instead of reducing either map. Limits
remain unchanged. The failed exact snapshot and log are retained.

Green selected source SHA-256:
`b55fbd034c2d54407684f1222d305b3d088cc19b8fefe2c9c536f412911ac658`.
Green selected olean SHA-256:
`9602ae5dfe701ca9dd02a65263ea5bff51478a86595697f783596156427d5b1d`.
Source, log, manifest use `experiments/selected-grs-submodule-nuc-v2`.
All five audits use only the same three standard axioms.

The final actual-message composition passed on its first attempt. It
imports the frozen submodule, interpolation, and primitive-factor leaves;
it does not reproduce their proof or assume their conclusion as a new
correspondence premise.

Final source SHA-256:
`17e1e0f7ff495c9ef124f39ca3461e869263fc9d7f32c1fb559694b8ac30b35b`.
Final olean SHA-256:
`01642a27f97e74a7548507112749e6e3f4883c0134f8604a7b56b38709d72f53`.
Source, log, manifest use `experiments/selected-linear-factor-recovery-nuc-v1`.
All three audits use only the same standard axioms. No recursion,
heartbeat, or memory cap was raised in any of these attempts.
