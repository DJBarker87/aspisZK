# Identity-branch factor coherence and its remaining exceptions

Research parent: `f0f46ffede8812252ac7cee9edf5547f228533d5`.
This is a continuation of [the component OOD reduction](component-ood-continuation.md),
not a new global soundness or extraction claim. No production source changes,
new prover messages, query changes, work credit, or size allowance are involved.

## Primary result: a finite identity-factor cover without a regularity premise

The checked `experiments/FactorIdentityCover.lean` strengthens the regular-only
bridge below. For any fixed nonzero parent `P`, two fixed OOD points, and two
polynomial answer curves of degree at most `c`, it **constructs** one nonzero
exception polynomial `E(Z)` with

    degree(E) <= weightedDegree_(Z+cY)(P).

Uniformly over every later gamma and every arbitrary adaptive horizontal
polynomial candidate `U(X)`, a parent root and the two actual point equalities
imply

    E(gamma)=0
      OR
    U is a root of a positive-Y prime factor F of the fixed parent P,
    and BOTH complete OOD answer identities hold for F.

The factor universe is fixed before OOD, and the retained subset and exception
polynomial are determined by the two OOD points/answers before gamma. No
candidate is selected or frozen early. No parent OOD-identity premise is needed:
the theorem works for arbitrary answers, and so can replace, not be added to,
the earlier `117077` gamma exception after the selected degree instantiation.
The selected source adapter and probability composition are root-owned work;
this new leaf itself is the generic exact algebraic cover.

The proof constructs a polynomial for **each actual fixed prime factor**:

- For a positive-Y factor satisfying both identities, use `1` and retain it.
- For a positive-Y factor excluded by either row, choose one nonzero actual
  OOD substitution polynomial from those rows.
- For a Y-constant factor, use the leading X-coefficient, a nonzero polynomial
  in Z, after swapping the coefficient polynomial's X/Z order.

The last branch explicitly handles content and zero specializations. A
horizontal root of a Y-constant factor makes that chosen coefficient vanish.
The product of all selected nonzero polynomials is nonzero, and a mapped
factorization of the parent forces an adaptive root either into the retained
family or into that product's roots. Each selected polynomial's degree is
bounded by its own factor's weight. The all-factor weight sum is at most the
parent weight, reusing the multiplicative argument already present internally
in V7's positive-factor budget proof. There is no factor-count multiplier,
separate content charge, derivative assumption, or hidden supplied beta premise.
Repeated factors consume only their multiplicities already present in the
parent weight; singular honest-compatible factors are retained normally.

This family consists of global polynomial factors, **not** recovered component
tuples or checked witnesses. Efficient factorization, authenticated-word access,
the real Fiat–Shamir experiment, and factor-to-message recovery are not proved.

## Complementary regular single-factor bridge

The checked `experiments/FactorCoherence.lean` uses the existing V7 trivariate representation
`K[X][Z][Y]`, its `specializeEvaluationPoint` and `challengeCandidateHom`, and
the fixed `curvePrimeFactors` multiset. Compilation status is recorded below.

For fixed nonzero `P`, the actual OOD point `t`, and the complete answer
polynomial `A(Z)`, define

    answerHom(P) = P(t, A(Z), Z)
    D(Z) = (partial P / partial Y)(t, A(Z), Z).

If `answerHom(P)=0`, the new endpoint retains `D=0` explicitly. Otherwise it
selects a positive-Y global prime factor `F` of `P` **before gamma** such that
`answerHom(F)=0`. Uniformly for every later gamma and every adaptive polynomial
`U(X)`,

    P(X,U(X),gamma)=0,
    U(t)=A(gamma),
    D(gamma) != 0
      => F(X,U(X),gamma)=0.

This is not a supplied candidate-family or component-tuple hypothesis. Factor
existence comes from the fixed global factorization and the whole OOD identity.
A nonzero derivative curve also excludes a zero whole-parent specialization at
`X=t`, which is needed to rule out a constant-in-Y factor vanishing there.

The core proof is the product rule. Write `P=F*H`. If the candidate is not a
root of `F`, the integral domain `K[X]` forces it to be a root of `H`.
At the shared OOD value both factors then vanish, so the parent Y derivative
vanishes. No received-word polynomiality, degree bound on `U`, squarefreeness,
or source/replay oracle access is assumed.

The identity also supplies the literal monic degree-one local divisor
`Y-A(Z)` of `P(t,Y,Z)`. This does not identify it with the normalized
representative in V7's chosen prime-factor multiset or prove all prerequisites
of the existing Hensel construction.

The root-owned `CurveOODDerivative.lean` addresses the separate quantitative
step: the selected weighted derivative has degree at most `117049`. A nonzero
polynomial degree bound does not bound the retained **identically zero** branch.
No derivative exception is silently charged twice across the two OOD points.
Singularity is a classification remainder, not necessarily an error or rare
event: an ordinary honest-compatible interpolant `(Y-U(X,Z))^3` has identically
zero derivative along its true answer curve. This theorem does not claim to
place all honest or all invalid executions into its regular branch.

## What the older Hensel theorem actually requires

The useful pinned sources are under `AspisFormal/AspisFormal/K1/`:

| Source | Relevant exact endpoint |
| --- | --- |
| `V7ExactCorrelatedAgreementFactors.lean` | Fixed global factorization and positive-degree factor root selection |
| `V7ExactCorrelatedAgreementSmooth.lean` | Nonzero factor resultant; literal simple specialized roots; X/Z certificate degrees |
| `V7ExactCorrelatedAgreementPowerSeriesLift.lean` | Power-series root for one fixed smooth global/local branch |
| `V7ExactCorrelatedAgreementRegularHensel.lean` | Nonzero regularized derivative and explicit local pole set |
| `V7ExactCorrelatedAgreementFactorBudgets.lean` | Actual Hensel evaluation numerator, not a security theorem |
| `V7ExactCorrelatedAgreementConcreteBranch.lean` | Literal 29-message recovery after valid-response, fixed-branch, simplicity, pole, and cardinality hypotheses |
| `V7ExactCorrelatedAgreementOuterSelection.lean` | Old global/local branch selection, choosing its own smooth point |

The old outer-selection theorem chooses a suitable smooth evaluation point;
it does not automatically apply with the actual sequentially sampled OOD point.
The concrete initial-branch theorem also requires actual `Width29ValidResponse`
on a sufficiently large selected gamma set, membership of every selected
candidate in the same global and local branches, simple roots, excluded poles,
and the corresponding power-series specialization. Its returned components are
literal original-code messages, but these premises cannot be dropped.

For `Y-A(Z)` with `deg A<=28`, the local degree is one, the weight is 28,
and its leading coefficient is one. Hence its own local pole set is empty.
The literal V7 per-branch evaluation expression simplifies to

    B(W) = 28 + 2047*(W-28),     W <= 117077,
    B <= 239599331.

This is only one numerator inside the old argument. The existing literal
initial-component theorem requires

    selected.card > 29*B + (28*1048576+1),

which at that ceiling is `6977740728`, not `239599331`. These are elementary
integer substitutions into the proved budget definition, not new probability
certificates. Dividing either number by a challenge-space cardinality would
still omit the branch-selection, regularity, source sampling, and extraction
obligations. No 100-bit conclusion follows.

The directly available coarse factor certificate bounds are

    deg_X certificate <= (d + deg_Y derivative)*deg_X factor,
    deg_Z certificate <= (d + deg_Y derivative)*deg_Z factor.

At the initial bounds `d<=111`, `deg_X<=114687`, `deg_Z<=117077`, these give
`25345827` and `25874017`, respectively, for a single worst-case factor.
Charging actual OOD-point exceptions needs the actual bounded sampler law and
its sequential conditioning; the ideal full-field law cannot be substituted
without that bridge. Summing over factors or combining both points also needs
a proved partition/additive accounting.

## Countermodels: preserve the compatible-candidate premise

These are algebraic diagnostics, not payment forgeries or measured acceptance
rates. No secrets, real owners, or witnesses are published.

1. `P=Y^2-X` can have polynomial-in-gamma roots after suitable X
   specializations, but has no polynomial horizontal candidate `U(X)`.
   It therefore does **not** refute a theorem requiring the actual compatible
   original-code candidate.
2. `P=Y^2-gamma*X^2` has polynomial horizontal candidates at square gammas,
   but at a nonzero OOD X its right-hand side has odd degree in gamma, so no
   polynomial answer identity exists. It also fails the combined premise.
3. `P=Y^2-(X-a)*(gamma-b)^2` does satisfy both identities at points
   `t_r-a=s_r^2`, using `A_r=s_r*(gamma-b)`, and has the compatible candidate
   `U=0` at gamma `b`. No global polynomial component curve exists. The
   specialization at `b` is singular, showing why an exception is necessary.

There is a stronger pole obstruction with fixed exact C1 and a quadratic
three-helper curve. Choose nonzero `b` and an `a` outside the stored GRS points.
On the normalized stored domain set all C1 lanes to zero and helper lanes to

    lane26(x_i) = -b/(x_i-a),
    lane27(x_i) =  1/(x_i-a),
    lane28(x_i) =  0.

The normalized raw batch is `gamma^26*(gamma-b)/(x_i-a)`. Put

    H(X,Y,gamma) = (X-a)*Y - gamma^26*(gamma-b),
    P = H^3.

At every stored point `P` vanishes to total multiplicity three on the raw
curve: `H` is in the point ideal, hence `H^3` is in its third power.
Thus this polynomial has the **shape of an actual symbolic multiplicity-three
interpolation-kernel element**, including all six mixed Hasse constraints,
not just the zero-order root condition. Its monomials obey the actual bounds:
`X+1024Y <=3075 <114688` and `gamma+28Y <=84 <117078`.

For either OOD point `t!=a`, the polynomial
`A_t(gamma)=gamma^26*(gamma-b)/(t-a)` has degree 27 and gives an identity.
At the nonzero actual gamma `b`, the horizontal candidate `U=0` is an
original-code message and agrees with every stored symbol and both OOD values.
The squarefree factor `H` has nonzero derivative `t-a` at those OOD points.
Nevertheless no polynomial `B(X,gamma)` can be its global root: substituting
`X=a` into `(X-a)*B=gamma^26*(gamma-b)` would equate zero with a nonzero
polynomial. Two OOD identities therefore do not automatically turn a rational
branch into polynomial message coefficients, even after factor regularization.

This construction does not assert that the current `Classical.choose`
interpolant selects `H^3`, that all field-level words are source-authenticated,
or that the zero C1 table is a valid payment. The literal source normalization
is invertible on stored symbols; an actual committed/proved fixture remains
unbuilt. The Hasse-kernel calculation is a mathematical argument, not a new
retained Lean kernel-membership theorem. The checked small polynomial regression
`RationalHelperIdentity.lean` proves the degree-27 numerator and exact helper
factor, both nonpole OOD identities, their compatibility with the zero
horizontal polynomial at gamma `b`, and the absence of any global polynomial
component curve solving either the cleared equation or its cube. Those are
generic field identities; the selected kernel/domain/source adapters remain
separate mathematical arguments.

There is also a mathematical way to avoid reliance on the chosen interpolant:
for any kernel `P` of Y degree `d<=111`, clear `(X-a)^d` in the substitution
`Y=N(Z)/(X-a)`, where `N(Z)=Z^26(Z-b)`. The resulting polynomial `S(X,Z)` has
X degree at most `114687+111=114798`. The zero-order kernel identities make it
vanish at all `1048576` distinct stored X points as a polynomial in Z.
Consequently `S=0`, and every nonpole OOD point gives an identity for that same
kernel `P`. This uses only the fixed domain, zero-order kernel equations and
weighted degree bound, but the denominator-clearing/root-count adapter is
**not formalized in the retained leaves**. It must not be reported as a
checked source theorem. The special gamma can be counted by a future bound;
a zero-exception implication is what the construction rules out.

## Precise next obligation

Neither checked factor cover forces
polynomial-in-X coefficients from a retained factor or a regular linear local branch. The next
needed theorem must either produce literal code-valued components from the
actual compatible candidates or explicitly count the specialization/pole
cancellations that prevent doing so. It must work with the actual pre-OOD
interpolation-kernel element and sequential OOD choices. Generic two-identity
factorization alone is insufficient, as the rational helper construction shows.

## Verification and provenance

`FactorCoherence.lean` is green and frozen. Its first focused check failed on
four local elaboration details: an implicit `eval₂_at_apply` argument, a
newline before an `Or.resolve_right` projection, omitted `derivative_map`
arguments, and the missing `C_zero` rewrite. The correction supplies exact
arguments and a targeted rewrite; no proof statement or resource limit was
changed. Failed logs retain the compiler's `sorryAx` diagnostics and are not
claimed as results. The successful v2 has seven standard-only axiom audits
(`propext`, `Classical.choice`, `Quot.sound`), with no new axiom or `sorry`.

| Focused target | Exit | Wall | Peak RSS | Swaps |
| --- | ---: | ---: | ---: | ---: |
| `factor-coherence-nuc-v1` | 1 | 3.41 s | 6801228 KiB | 0 |
| `factor-coherence-nuc-v2` | 0 | 3.61 s | 6834728 KiB | 0 |
| `rational-helper-identity-nuc-v1` | 1 | 1.06 s | 2024648 KiB | 0 |
| `rational-helper-identity-nuc-v2` | 0 | 1.18 s | 2035344 KiB | 0 |
| `factor-identity-cover-nuc-v1` | 1 | 3.30 s | 6806664 KiB | 0 |
| `factor-identity-cover-nuc-v2` | 0 | 3.40 s | 6843080 KiB | 0 |

The runner checked 717 source/olean/native-package provenance entries before
and after v2. Exact failed and successful source snapshots, logs, manifests,
and the green olean are local in `experiments/`. The source and olean hashes
match the remote successful result:

```
source   e1873ee972199296ccad61f45ad39019e2efbd62d468f5986b764596448b0b38
olean    e3d0a6bc21765992b42285194a767bf973523dfc12248c3cf6499a944bda1a83
manifest 0ddb6d02b92b9adf3d65c25626c9ec44503448513d25190f8aff520d535f371d
runner   7ed329de2a9fa09f7c0d41589c3a466156081bf0d392357262883667388c80ad
```

The rational-helper v1 diagnostics were an already-closed degree goal and an
over-eager subtraction rewrite inside the polynomial before evaluation.
Removing the redundant tactic and separating polynomial evaluation from the
scalar rewrite made v2 green, with unchanged statements and limits. Its seven
audits are also standard-only, and all exact v1/v2 snapshots/logs/manifests
plus the successful olean are local. The runner checked 721 entries before and
after this focused target.

```
RationalHelperIdentity source
7072cb88fcc1f17edaf125f7c49da9db4a67f54ebe1f14eb1cfb62057c78851f
RationalHelperIdentity olean
5630691af0bc5afecfccc9ac5694dfca0b323f1703fa30e87a68d752870d1560
rational-helper-identity-nuc-v2 manifest
3643959951ee287f5e03c74a47df455908ba1aa3e14e04d5746ebee942978c4d
```

The identity-cover v1 errors were an `as_sum_support` orientation, missing
`swap(0)=0` simplification, and a Nat preorder projection at transitivity.
The successful v2 uses the exact orientation, `map_zero`, and explicit
`Nat.le_trans`; no limits or statements changed. It checked 723 provenance
entries before and after the target, with seven standard-only audits.
Both versions' exact source snapshots/logs/manifests and the green olean are
local, and the copied hashes match the executed NUC artifacts:

```
FactorIdentityCover source
8a644896ba85fc515bafc9297664494f840aa91e1904c92da5a836d4681bde4d
FactorIdentityCover olean
e0110eb6cf6a3209b60c985faa7c044a1d127a20ceeede4bf509ec434dba307b
factor-identity-cover-nuc-v2 manifest
e5f5793096fecb6158572015d989a2f2eba3924b24b2c6b5252d5118179cd37b
```

Executed command, after staging only the new leaf:

```sh
ssh -o BatchMode=yes dombarker@nuc.local \
  'bash /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg/run_symbolic_ood_nuc.sh /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg FactorCoherence factor-coherence-nuc-v2'
ssh -o BatchMode=yes dombarker@nuc.local \
  'bash /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg/run_symbolic_ood_nuc.sh /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg RationalHelperIdentity rational-helper-identity-nuc-v2'
ssh -o BatchMode=yes dombarker@nuc.local \
  'bash /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg/run_symbolic_ood_nuc.sh /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg FactorIdentityCover factor-identity-cover-nuc-v2'
```

The retained runner rejects reuse of an existing log tag; reproduction needs
a fresh tag in the same pinned workspace. It executes only the named leaf,
with `lean -j1 -M9500`, in a serialized NUC scope with `MemoryHigh=8G`,
`MemoryMax=10G`, `MemorySwapMax=0`, and `CPUQuota=200%`. There was no laptop
compile, package rebuild, SBF build, dense arithmetic job, or unchanged replay.
The imported source pin is `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, the
research source pin is the parent above, and the native package cache boundary
is explicitly not a replay of package compilation.

The following inspected V7 source SHA-256 values are recorded; the imported
closure was checked against the immutable borrowed pin by the focused runner:

```
Factors       112e16cd05454f76e65958025ed01fd45e07dd2cf0632ee5eb53e2170b4ad8f3
Smooth        af4f75fd298825dc5d14f8315136bfd9d7bd550831dad834aa00e422b7a35c8a
PowerSeries   892af45824af2fab92db4e63454d82d25ae6231ac4b9ef5f6e7644fab8120db1
RegularHensel 411aa5c9e5098739238679ae52b073697cddd85097fbb0e14bc56fa9d94bea34
FactorBudgets ced62421bc10c37b03bbe780b0c7b94183ced4ddb1f42128aeb12637acab7866
ConcreteBranch 2dad4a8e9c07fddfaf0e92a08c57fe7ad65c418db758ae71f1e82b76018cd602
OuterSelection 39ba46f483a7c8b92db20577eb7121bec2bfb3ff3c38458c8ec2447c06c41e77
```
