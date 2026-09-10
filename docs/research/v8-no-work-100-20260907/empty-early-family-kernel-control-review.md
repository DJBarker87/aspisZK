# Empty early family despite a causal, row-correct middle candidate

## Result and exact scope

The optimized [exact control](experiments/EmptyEarlyFamilyKernelControl.rs) passes.
It constructs a fixed received word with an **empty** early C1 family, but a
later high-support codeword satisfying image, ordinary-row and two retained
polynomial OOD identities. Its degree-31 irreducible factor occurs in an
explicit multiplicity-three interpolation-kernel member and is regular at the
designated later challenge. Thus merely adding row correctness or kernel
compatibility does not repair a generic support-to-early-family implication.

This is a synthetic F181 Reed–Solomon model, not a counterexample to the full
selected Aspis theorem. In particular, its four-symbol groups are not the
literal circle fibres, its off-grid OOD points are not a verified instance of
the secure-circle accepted-parameter law, and the actual `fixedInterpolant`
selector is not connected. It demonstrates one good gamma, not a large
exception set or an attack on a claimed probability/payment bound.

## Fixed data, timing and empty family

Work over K=F181. Let D be the 90th roots of unity other than ±1: 88 distinct
points, none equal to 0 or 1. Use the RS code of polynomials of degree at most
2. In sorted order, group D into 22 groups of four. Let e(x)=0 on the first
19 groups and e(x)=1 on the last three. All this is fixed before gamma.

The 26 C1 lanes are `c0=e−X³`, `c1=X³`, and 24 zero lanes. The three helper
lanes are zero. With δ=gamma−1, the actual toy batch is

`R_x(gamma)=δ x³+e(x)`.

Every degree-at-most-two polynomial agrees with the fixed C1 lane X³ at at
most three points. Consequently every C1 tuple has joint support at most
three. The family is empty both at threshold 4 (the proportional small-grid
analogue) and at threshold 14. The latter also has an independent universal
Johnson list cap at most 52, hence at most 100: a hypothetical list of size L
would satisfy `20 L ≤ 1056`. Thus the control does not obtain emptiness by
using a threshold with an enormous permitted list.

The executable covers all codewords using an exhaustive witness reduction:
every quadratic having at least three agreements is the unique interpolant
through one of the 109,736 triples. Every such interpolant has exactly three
agreements. Quadratics with fewer agreements cannot enter either family.
This is not an enumeration of the 26-lane message universe.

At the later gamma=1, original candidate U=0 agrees on 76 symbols, or 19/22
full groups. This fraction is inside the selected middle ratios
200808/262144 through 252847/262144. Take the toy chord `L=X(X−1)` and
interpolant `I_gamma=δX`. Both are legal on D (there are no poles there).
At gamma=1, Q=0 reconstructs U=LQ+I=0 and its virtual quotient support is
exactly the same 19 groups. The zero quotient satisfies the image equations.

Fix all three claim polynomials, the inactive claim and the helper curve to
zero before gamma. The helper curve has degree 0≤2 and the claim polynomials
have degree 0≤28; these bounds are not interchanged. At gamma=1 every fixed
ordinary covector on U gives the claimed zero. The six compact response
coefficients and the final can be zero before alpha; the omitted quartic
coefficient `claim/4−c0` is zero as well. These are exact causal row/response
facts at the designated branch. They do not claim literal source row-weight
provenance, authentication, nonlinear payment relations or complete suffix
acceptance. No pre-gamma object is chosen using the realized gamma; gamma=1
is simply the branch where the fixed cancellation occurs.

## Higher factor, both OOD identities and the kernel

With indeterminate Z and δ=Z−1, define

`F(X,Y,Z)=Y^31−Y−X³(δ^31−δ)`.

At the two off-grid toy OOD points X=0 and X=1, the answer polynomials 0 and
δ are identities of F. Their lane coefficients can be fixed before gamma;
they do not require choosing a future challenge. At gamma=1, U=0 is a
polynomial-in-X root, and the Y derivative at both OOD branches is −1,
not zero.

F is irreducible, not merely a product containing a convenient linear root.
Over `K(Z)[Y]`, view it as a polynomial in `X`. Its nonzero leading
coefficient is a unit, and after making it monic the constant term is
`−(Y^31−Y)/(δ^31−δ)`. Eisenstein at `Y` applies: this constant has
`Y`-adic valuation exactly one, all intermediate coefficients vanish, and
the leading coefficient is a unit. Gauss and primitivity then give
irreducibility in the trivariate ring (F is monic in Y). The executable
checks the explicit valuation/nonzero-coefficient data; it does not implement
a general irreducibility prover. The argument here supplies that mathematical
step.

For x∈D, h=x³ satisfies h^31=h. Therefore every good received curve Y=δh
satisfies F identically in Z. Let `B(X)=∏bad x (X−x)` (degree 12) and choose
the fixed pre-OOD parent

`P(X,Y,Z)=F(X,Y,Z)^3 B(X)^3`.

At every good coordinate, F has zero constant X/Y Taylor coefficient along
the received curve; at every bad coordinate B does. Cubing kills every
mixed X/Y Hasse coefficient of total order below three. The program checks
all six **polynomial-in-Z** constraints at all 88 coordinates: 528 exact
zero polynomials, not equality as finite-field functions.

This uses precisely the six-constraint shape of the reused V7
[`curveConstraintPolynomial`](../../../AspisFormal/AspisFormal/K1/V7ExactCorrelatedAgreementInterpolation.lean)
definition. The explicit parent has Y degree 93, X+2Y weighted degree 222
and Z+28Y weighted degree 2604. Its 76 matching symbols exceed 222/3=74,
so it is also compatible with the toy interpolation root-coverage threshold.
The same monomials have X+1024Y weight 95268, below 114688, but that numeric
fact does **not** turn this 88-point grid into the actual million-point code.

There is a genuine selector gap: a different kernel member, for example
`(Y−δX³)^3 B³`, also exists. The source
[`SelectedOODGate.fixedInterpolant`](experiments/SelectedOODGate.lean)
uses `Classical.choose` from existence and exposes nonzero/kernel properties;
the fixture neither computes nor proves that this particular choice equals
P or contains F. It must not be presented as an actual `higherPrefix` witness.

## What the existing source bridges do and do not supply

- [`EarlyC1Family.actual_late_projection_member`](experiments/EarlyC1Family.lean)
  needs the reconstructed tuple's **own**, all-lane support ≥38228.
  Its `family_card_le_100` and base-field descent do not establish coverage.
- [`ClaimTransport.component_error_coeff`](experiments/ClaimTransport.lean)
  and [`Gamma29Reconstruction.reconstructed_claims_exact`](experiments/Gamma29Reconstruction.lean)
  recover the 87 scalar row claims once 29 nodal batches are represented.
  They do not recover agreement of committed C1 lanes with those components.
- [`NestedMiddleOwnSupportDichotomy.early_member_or_all_nodes_bad`](experiments/NestedMiddleOwnSupportDichotomy.lean)
  explicitly retains the alternative that all 29 interpolation nodes belong
  to the reconstructed tuple's own bad-gamma set. The tuple is postselected,
  so a fixed-target gamma bound cannot just be applied to its training nodes.
- [`ThreeHelperClaimCover.quotient_cover_dichotomy`](experiments/ThreeHelperClaimCover.lean)
  needs the strong fixed `earlyC1=some p`, not merely membership in the weak
  100-element family. Weak support 38228 plus middle original support 803230
  need not intersect at all on 1048576 symbols, so replacing that premise by
  weak family membership does not recover the three helper components.

The missing useful premise is source-derived, same-candidate component
recovery: a tuple fixed before the charged gamma with
`original(Q_gamma)=batch gamma tuple`, together with enough own support to
place its C1 projection in the fixed family (or a separately charged failure
of one of these properties). Even pointwise weak-family membership alone
would not fix the helper tuple across gamma. A blind factor 100 cannot replace
either implication.

One available conditional repair is
[`MiddleCoherentIncidence.coherent_37_early_member`](experiments/MiddleCoherentIncidence.lean):
37 distinct middle nodes represented by the **same** tuple force membership.
The first 29 are interpolated tautologically; the additional eight are not
known to be represented. A fresh, explicit coherence holdout would be a new
source/causal obligation, not a consequence of ordinary row correctness.
An offline extraction experiment changes no transcript bytes or CU, but
also gives no acceptance bound without that obligation. Adding a verifier
holdout changes the protocol and needs its own byte/CU accounting.

No smaller source-valid gamma numerator follows from this control. In fact
only gamma=1 has a high-support degree-at-most-two candidate here: for δ≠0,
any such candidate matches at most three good points plus the twelve bad
points. Therefore this is a deterministic implication regression, not an
obstruction to proving a sharper row-qualified gamma tail. The currently
missing approximately 7.07-fold numerical improvement remains unproved;
there is no new 100-bit theorem.

## Reproducible bounded evidence

Run from source parent `5cadd01c7af31a8ebe1a00e4bfed77c1e9c77b59`, on the
ordinary local Darwin arm64 development machine, with rustc 1.93.0:

`rustc --edition=2021 -O -C overflow-checks=yes SOURCE -o BINARY`

The [frozen runner](experiments/empty-early-family-kernel-control-local-v1-runner.sh)
sets 60-second CPU and small file/descriptor limits. This tiny local job is
not represented as a Linux cgroup or swap-disabled NUC job. No NUC connection,
Lean build, dependency replay or axiom audit was performed.

| Stage | Exit | External wall | Peak RSS | Reported swaps |
|---|---:|---:|---:|---:|
| Optimized compile | 0 | 0.79 s | 128778240 bytes | 0 |
| Exact control | 0 | 0.64 s | 1916928 bytes | 0 |

The arithmetic's internal timer is 0.074582 s. SHA256 inventory:

- Source and [frozen source](experiments/empty-early-family-kernel-control-local-v1-source.txt):
  `d928e87832d4da4ce597c3e309dd8ede776d6192652e7c83169c1774c6e8554c`.
- Live/frozen runner:
  `e3fac51fc13fe088e9c0abe2af77cdc2b047a162ea136cde04a82e2512900de7`.
- [Terminal log](experiments/empty-early-family-kernel-control-local-v1.log):
  `1fa2b09ad4a7afc8ea2e12da5141dfd4e04aadce53ef976962b078a50a1c9abf`.
- Executed temporary binary, recorded in the log, not required or committed:
  `b0654df03a0284b8d9463fcc1c45af41aa812cce53285f08df781755a885e0d6`.

The result is exact executable evidence plus the stated elementary algebraic
argument, not a Lean-certified irreducibility/selected-protocol theorem. No
new generic Lean wrapper was added: the missing source recovery, rather than
the already elementary empty-family implication, is the substantive next task.
