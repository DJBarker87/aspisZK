# Identity-coordinate threshold and an early-C1 obstruction

Source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: exact arithmetic and a restricted F127 control checked by the
optimized, capped NUC regression described below. No new Lean theorem is
claimed here.

## Exact uniform-gamma threshold

The checked `SupportQualifiedRootIncidence.adaptive_polynomial_bound` gives,
for b<a,

    n <= floor(W*(T-b)/(a-b)).

With T=1048576, a=38230, W<=117077, P=2147483647 and nonzero gamma domain
of size L=P^4-1, the sharp consequence of this inequality alone is

    probability <= min(L, floor(117077*(1048576-b)/(38230-b))) / L.

For b>=38230 the incidence theorem supplies no nontrivial cap. Uniform
gamma is an explicit model premise; no source sampler law is supplied by
this calculation.

The maximum allowed integer numerator for100 raw bits is

    M = floor(L/2^100) = 16777215.

The floor bound is at most M exactly when

    (16777216-117077)*b < 16777216*38230-117077*1048576.

Thus the maximum certified identity count is **31129**.

| b | Exact gamma cap | Displayed raw bits |
| ---: | ---: | ---: |
| 0 | 3211198 | 102.3853198047 |
| 31129 | 16775051 | 100.0001861805 |
| 31130 | 16777397 | 99.9999844330 |
| 38229 | 118288395719 | 87.2164824036 |

The maximum-b calculation is integer arithmetic, not rounded logarithms.
At b=31129 the strict-integer-inequality margin is15368397; at b=31130 it
is -1291742. The displayed logarithms are explanatory only.

There is no necessary factor-count loss: since (T-b)/(a-b) increases with b
when T>a, a finite family with b_F<=31129 and sum W_F<=117077 has union
cardinality at most the same16775051. Sum the incidence bounds and use
`card_union <= sum cards`. This is a mathematical aggregation consequence,
not a newly checked family theorem. Factors with b_F>=31130 remain an
explicit residual class.

## What fixed early C1 actually supplies

`EarlyC1GaoRecovery.badFibres_card` derives at most16535 bad complete fibres
from `earlyC1 c1=some p`; equivalently up to66140 symbols can lie outside
the complete-fibre own support. `FixedC1HelperReduction.raw_batch_on_c1_support`
and `restricted_support_iff` apply only where all26 received C1 lanes equal
the fixed codeword. `FixedC1FarMoment.raw_on_own_support` preserves that
restriction and the actual quadratic helper curve.

Consequently b>=31130 does **not** force even one identity coordinate into
the known-C1 support. The general lower bound for that intersection is only

    max(0,b-66140).

Even b=38230 may be entirely excluded. It is therefore invalid to globally
subtract early C1 on this large-identity branch or infer a helper-only
polynomial section from its size. `EarlyC1Specialization.identify` is the
existing converse identifying the optional object from sufficiently large
actual own support; closeness is not merely an informal decoder choice.

## Restricted exact cubic regression

Work over F127. Use100 distinct evaluation coordinates grouped in their
listed order into25 four-symbol fibres. Let B={2,3,4} lie in the first
fibre, and fix parameters t0=1,t1=8 outside the coordinate domain. Define

    H(X) = 1 + (X-1)(X-2)(X-3)(X-4)(X-8),
    R(Z) = Z(Z-1),
    F(X,Y,Z) = Y^3 - R(Z)^3*H(X).

H has ascending coefficients [63,43,51,115,109,1], degree5, and no zero
on the100 coordinates. Received C1 has lane1=-1 and lane2=1 on B and is
zero everywhere else; all other C1 lanes and all three helper lanes are
zero. Thus raw=R on B and0 elsewhere, fixed before gamma. The helper curve
has degree0<=2, and the full component/answer curve has degree2<=28; no
claim is made that generic component errors have degree2.

The fixed pullback is identically zero exactly on B. All three identity
coordinates are outside the early-zero own support, which contains24/25
complete fibres. The selected-model threshold scaled to25 fibres is
ceil(245609*25/262144)=24. For the degree<=2 evaluation code, zero is the
unique qualifying scalar codeword for each of the three distinct C1 lane
patterns. The new Rust checker exhausts all127^3 degree<=2 messages for
each pattern,6145149 checks in total; the other23 lanes duplicate the
zero pattern. This is a small-code analogue of the existing optional
uniqueness constructor, not an invocation of the actual QM31 decoder.

Both predetermined OOD parameters satisfy H(t)=1, so the same polynomial
answer R(Z) gives exact retained section identities. At gamma=1 the actual
polynomial candidate U=0 agrees at every coordinate and at both OOD points.
For gamma outside{0,1}, a polynomial root would satisfy
U(X)^3=nonzero_constant*H(X); degree5 cannot equal3*degree(U), so no such
polynomial exists. The same degree obstruction over an algebraic closure's
fraction field shows that the cubic is absolutely irreducible: after
inverting R, its equation is V^3-H(X), which has no rational root.
This irreducibility explanation is mathematical, not a Lean or runtime
factorization theorem.

The kernel restriction is not ignored: P=F^3*Y^3 has multiplicity at least3
along every received coordinate curve. The checker computes all six
total-order<3 bivariate Hasse coefficients in X and Y, as polynomials in Z,
at every coordinate,600 exact coefficient checks. The inherited selected
weighted bounds would allow this algebraic P: its X+1024Y weight is12288
and its Z+28Y weight is336, below114688 and117078 respectively.

This control falsifies the inference

    many identity coordinates + fixed early C1 + quadratic helpers
    + two retained cubic sections + a compatible specialization
    => identity coordinates meet early-C1 support / a global component root.

It does not falsify a theorem that also uses some unverified distinguishing
property of the **canonical chosen** interpolant. H, F, received lanes and
the designated parameters are fixed before any draws. The control does not
let H depend on future random OOD points, nor claim a lower bound on drawing
those designated parameters. No source acceptance, selected circle encoder,
authentication, semantic witness or payment assertion is made.

The set-placement obstruction is not an artifact of the toy percentages.
A symbolic selected-size template takes31130 coordinates in7783 fibres,
predetermined admissible t0,t1 outside the domain, and
H=1+eta*V_B(X)*(X-t0)*(X-t1). A nonzero eta avoiding at most T-b forbidden
values makes H nonzero on the entire coordinate domain; the actual field
has more than enough elements for this finite avoidance. Degree(H)=31132
is not divisible by3. The same F and P then have exact identity count31130,
zero-C1 own support254361>=245609, and a compatible U=0 at gamma1.
P's X+1024Y weight is96468<114688 and its Z+28Y weight is336. Undoing the
fixed nonzero GRS coordinate multipliers realizes the displayed normalized
received values as actual-shaped stored lanes. This is a mathematical
template, not an executed large instance or a checked canonical-parent
selection/accepted-source theorem.

## Evidence and next boundary

[`IdentitySupportCubicControl.rs`](experiments/IdentitySupportCubicControl.rs)
performs exact coefficient tests and exhausts the stated finite domain;
it is restricted to one fixed cubic, not an exhaustive search over factors.
The initial orchestration check covered12700 coordinate/gamma values,
254 OOD values and100 actual-zero-candidate checks. The Rust version adds
the600 symbolic Hasse tests and6145149 degree2-codeword checks.

The dedicated runner used optimized `rustc -O -C overflow-checks=yes`,
MemoryHigh1GiB/MemoryMax2GiB/SwapMax0/CPU200% and a60-second CPU limit on
Tailscale host `dombarker@100.108.41.90`. Compilation exited zero in 0.38s
with peak RSS134,220KiB; the control exited zero in 0.02s with peak
RSS1,936KiB and zero swaps. Its output records all6,145,149 codeword checks,
12,700 pullback evaluations,600 Hasse coefficients,254 OOD evaluations and
100 gamma-one candidate evaluations. These counts establish the stated
finite control, not a probability theorem.

- Source SHA256:
  `fcefe508cedebd8b481ac8a2c4ac75426d0fe3acfcf15ff390d11c042cc7ac4d`.
- Runner SHA256:
  `8065bf323365e6c1b84a7a831b5de12176f6e566250cc73fb272ba8c9a982c4c`.
- Run-log SHA256:
  `1ccc6f22074be6a3e5d66c12045950fd7e5dc1e9eff6daf10c20e01b15532585`.

The reproducible evidence is the Rust source, exact per-run source snapshot,
frozen runner snapshot and log. The platform binary is neither required nor
committed; its executed SHA256 is recorded in the log as
`7b731e2f90b199a07a9cf0ccb340d3f81058dd063529d20d3fd2dd6b5f444ffb`.
No local binary-retention or cross-platform binary-reproducibility claim
is made.

No generic identity theorem is drafted merely to rename the remaining
source gap: a useful new theorem must exploit more than b>31129 and
early-C1 closeness.
