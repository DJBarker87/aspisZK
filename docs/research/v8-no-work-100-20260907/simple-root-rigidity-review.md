# Simple-point rigidity for retained higher-degree branches

Parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Status: both focused leaves are checked and frozen, with seven standard-only
axioms audits. The transport failure and failed selected attempt are retained
separately from the successful evidence.

The checked generic leaf [SimplePolynomialRootRigidity](experiments/SimplePolynomialRootRigidity.lean)
proves that two polynomial roots with the same image under a coefficient
homomorphism are equal whenever the derivative at that image is nonzero.
Its proof divides by the first monic linear root factor, then uses the
product rule. It does not require a prime parent, monicity of the parent,
or a degree bound on the two candidates.

The checked source adapter [SelectedSimpleRootRigidity](experiments/SelectedSimpleRootRigidity.lean)
applies this to the actual selected original-message GRS polynomials.
`SelectedIdentityCover.literal_candidate` derives each candidate's value
at either actual OOD point from the same checked chord/image reconstruction.
The adapter does not accept a supplied equality of candidate roots or an
assumed original-code representation by a component tuple.

The exact conclusion is original-message equality for candidates lying on
the same factor at the same gamma and OOD prefix, under nonvanishing of that
factor's derivative at the actual normalized answer. Candidate quotients
may be indexed by alpha or by arbitrary later choices. No final is assumed
fixed before alpha. This does not establish quotient uniqueness, a
degree-28 message curve across gamma, received-word polynomiality, or a
bounded extractor.

## Remaining higher-Y event

`SelectedLinearCover.HigherDegreeRoot` supplies a retained positive prime
factor of degree at least two, plus a horizontal root for the same adaptive
Q. That predicate alone does not supply the candidate's actual OOD values.
The selected adapter therefore retains checked/circle/west exclusions,
literal covered-family membership and image validity, and derives those
values using the existing source theorem.

Derivative regularity is explicit. Neither both OOD polynomial identities
nor primeness makes every concrete gamma specialization simple. The earlier
example `Y^2-(X-a)*(Z-b)^2` has both polynomial OOD identities and the
compatible horizontal candidate zero at gamma b, where it is singular.
The checked RationalHelperIdentity/Specialization regressions also prevent
turning local regularity and two identities into a global polynomial
component curve without handling rational specialization exceptions.

One potential next source-shaped decomposition uses a product of the
existing V7 prime-factor derivative resultants. A nonzero coefficient fixes
an obstruction before OOD; outside roots at both actual points, choose one
point before gamma and retain its nonzero gamma certificate's roots.
This can discharge the current derivative premise for all retained factors,
but is not implemented by these two leaves. Repeated factors of the parent
must be handled via prime factors, not an assumption that the parent is
squarefree. The older OuterSelection theorem chooses its own smooth point;
it does not establish the actual sequential OOD sampler law.

The literal degree-two helper curve is unchanged. Its subtraction applies
only for exact C1 or on established C1 agreement support. The complete
component-claim error remains degree 28, including the degree-25 C1 error
after division by gamma^26. None of these degrees is replaced by a constant
or a retrospectively chosen polynomial target here.

## Independent quadratic-proposal audit

The proposed discriminant decomposition `D=a(Z)*H(X,Z)^2*R(X,Z)` needs a
polynomial factorization with explicit degree accounting, not just a
squarefree factorization over K(Z). If all Z-only content is in a and H is
X-primitive, H specialized at gamma cannot be the zero polynomial: that
would make Z-gamma divide every X coefficient. Otherwise a fixed nonzero
coefficient of H supplies an additional exceptional set of size at most
degZ(H). The cases a(gamma)=0 and leadingX(R)(gamma)=0 must also remain.

For positive X degree m of R, away from these cases, a square D at gamma
makes R at gamma a scalar times a square. With characteristic larger than
m, its specialized derivative has the expected degree, and the gcd has
degree at least m/2 when m is even; odd m cannot occur without degree drop.
The crucial new proof obligation is multiplicity of the Sylvester
determinant at gamma at least its specialized corank. A theorem saying only
that the resultant vanishes does not give the proposed X-degree cancellation.

With those lemmas, the proposed cost
`degZ(a)+degZ(H)+5*degZ(R) <= 5*degZ(D)` is compatible with additive
polynomial degrees. In the X-constant parity branch, primeness of the
quadratic must first imply that a is nonsquare in K(Z); the actual OOD
square identity then forces H(t,Z)=0 and a fixed coefficient obstruction.
These are an audit of a theorem proposal, not checked new degree/count
results or a probability certificate.

An explicit diagnostic for the omitted-H case is
`D=(Z-1)^2*(X^2-Z)`, with `a=1`, `H=Z-1`, `R=X^2-Z`.
At gamma 1, D is the zero square while `Res_X(R,R')=-4Z` is nonzero
in odd characteristic. Moving the Z-only square into a restores the
required content exception. This is an algebraic specialization diagnostic,
not an actual two-OOD transcript or a payment forgery.

## Verification

The generic attempt `simple-polynomial-root-rigidity-nuc-v1` completed
successfully: exit 0, 0.92 seconds, peak RSS 1,919,440 KiB, zero swaps.
Its three axioms audits use only the standard axioms (the first uses
`propext` and `Quot.sound`; the other two also use `Classical.choice`).
The unused `IsDomain R` section-variable warning in the first helper is
retained without an unnecessary source change or replay.

```
source  2fdf8fface7330588fe616543e18d66019e39118b1dc50c0bad9d53a3852dc85
olean   eea5b46423a97cfa0906dec1481c2759ac5189867fe461ae61378e4a53bc8b64
```

The fresh higher-Y NUC scope uses the same MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, CPU 200%, Lean `-j1 -M9500` limits.
Research parent and borrowed immutable V7 source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5` are recorded in each manifest.
Exact source snapshots, logs, manifests and green outputs are retained.
No laptop, cold dependency, or package-wide compilation was used.

The selected v1 launch produced no remote header or Lean output. At an
observed 18:23 elapsed, work paused for the mandatory review. A bounded
read-only probe failed to resolve `nuc.local` (exit 255). The stalled local
SSH process was terminated explicitly (exit 143), preventing a delayed
start. This is transport evidence, not a failed theorem check. See
[the exact launch record](experiments/selected-simple-root-rigidity-nuc-v1-transport.txt).
No selected theorem or selected axioms audit is claimed from that attempt.

The parent subsequently verified that no higher-Y process or selected v1
log existed. All further remote access used the verified Tailscale endpoint
`100.108.41.90`, with `StrictHostKeyChecking=yes` and `HostKeyAlias=nuc.local`
only for pinned host-key verification; the transport was not mDNS.
The concurrent V7 build remained separately capped and was not interrupted.

Selected v2 ran over Tailscale and finished exit 1 in 5.08 seconds, peak
RSS 6,784,692 KiB, zero swaps. All four theorem audits passed; the sole
error was a missing plain `end` for the unnamed noncomputable section.
The exact failed source, manifest and log are retained. Adding that one
closing line changed no theorem, tactic, numerical bound, or resource limit.

Selected v3 completed exit 0 in 5.37 seconds, peak RSS 6,815,616 KiB,
zero swaps, with all four audits using only `propext`, `Classical.choice`,
and `Quot.sound`. The runner checked 797 provenance entries before and
after the target and reported the overlay unchanged.

```
SelectedSimpleRootRigidity source
8328580e952cbb574f9b823187ac503d546f154b0b95f29cbdf64e5213fb46eb
SelectedSimpleRootRigidity olean
a5e2e5561c205f1a632f7e70f396de6c5c680adc0a6204c7e0a3360df4e9d825
selected-simple-root-rigidity-nuc-v3 manifest
310033f60de58ff4d68237675bd31e841719f78c6eb0563f18d7f833186e3fda
runner
5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52
```

The public selected endpoints are `original_unique` and
`adaptive_original_unique`; derivative regularity remains a hypothesis.
There is no new gamma exception count, higher-Y coverage bound, code-valued
component curve, source/authentication coupling, or payment extraction claim.
The build slot was released after the successful postflight. No unchanged
generic replay, wider manifest replay, or further target was launched.
