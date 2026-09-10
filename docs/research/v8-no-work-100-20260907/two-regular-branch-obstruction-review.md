# Two regular retained branches need not give coprime discrepancies

Status: exact optimized small-field control PASS; the general argument below
is mathematical/source analysis, not a new Lean theorem. This is a
factor-aware obstruction to an automatic coprimality step, **not** a
counterexample satisfying the literal selected interpolation parent,
middle support, `earlyC1 = none`, or payment-semantic acceptance.

## An absolutely irreducible retained cubic

Let K be any field of characteristic not two, let `0 != b(Z) in K[Z]`, and set

```
F(X,Y,Z) = Y^3 - Y - b(Z)*X*(X-1).
t0 = 0, t1 = 1, A0(Z) = A1(Z) = 0.
```

This F has Y-degree three. Both literal point substitutions vanish
identically, so it satisfies `FactorIdentityCover.Retained` for these two
points/answers. Its Y-derivative at either section is the constant -1,
hence **both sections are regular at every gamma**, with no derivative or
pole exceptional set. These are rational GRS evaluation-coordinate points;
they are not being identified with a particular sampled QM31 circle pair.

Absolute irreducibility does not require b squarefree, nonconstant, or
irreducible. Over the algebraic closure of K, regard F as a polynomial in X
over `Kbar[Z,Y]`. Its three coefficients are `-b, b, Y^3-Y`, whose gcd is one:
every factor of b depends only on Z, and none can divide the monic polynomial
`Y^3-Y`. It is therefore primitive. Over `Kbar(Z,Y)`, its quadratic
discriminant is

```
b(Z)^2 + 4*b(Z)*(Y^3-Y).
```

This has Y-degree three and therefore odd valuation at Y-infinity. It cannot
be a square in `Kbar(Z)(Y)`. The quadratic criterion and Gauss's lemma prove
irreducibility over `Kbar[X,Y,Z]`. The nonzero-b and characteristic-not-two
hypotheses are essential to this argument. Characteristic three is allowed:
the Y-derivative at the sections is still -1.

## Reflection identifies the two finite discrepancies

The exact identity `F(1-X,Y,Z)=F(X,Y,Z)` holds. Let S0(u) and S1(u) be the
unique formal roots with constant term zero at X=0 and X=1 respectively.
They exist and are unique because the derivative is -1. Reflection gives
`S1(u)=S0(-u)`, coefficient by coefficient. Equivalently, if `c_n(Z)` is the
n-th coefficient of S0, the corresponding coefficient of S1 is
`(-1)^n*c_n(Z)`.

For **every common truncation length N**, evaluation at the midpoint has

```
sum(n<N) c_n(Z)*(1/2)^n
  = sum(n<N) ((-1)^n*c_n(Z))*(-1/2)^n.
```

Both local factors are the literal monic `Y-0`. Under their canonical
identification with the scalar coefficient ring, both regularized Hensel
derivatives are -1. Thus V7's denominator-clearing powers are identical too.
Subtracting the same received-coordinate polynomial R(Z) gives **identical
cleared discrepancies D0(Z)=D1(Z)**. This applies also when R has degree at
most 28, including R=0. A resultant or gcd of these two discrepancies cannot
be declared nonzero/coprime merely because the OOD points are distinct and
both roots are regular.

This directly concerns the constructions in
`V7ExactCorrelatedAgreementBranchEvaluation.clearedFiniteBranchDiscrepancy`
and its `specialization_clearedFiniteBranchDiscrepancy_eq_zero`. It is not
an argument involving the different parent separability resultant.

## Exact finite control

`experiments/TwoRegularBranchControl.rs` uses F65537 and constructs both
length-17 formal series as **polynomials in a formal parameter T**, not by
fitting sampled values. It verifies all coefficients of each defining
equation modulo u^17 and all 17 reflection identities. At the midpoint,
the two discrepancy polynomials coincide, are nonzero, and have T-degree 15.
The derivative-clearing exponent is 31.

Next substitute `b(Z)=product(g=1..37)(Z-g)`. Exact polynomial composition
gives a nonzero degree-555 discrepancy divisible by b. The code verifies
that division identity and all 37 common roots. At each such gamma the
specialized global factor admits the original polynomial U(X)=0, which
meets both zero OOD answers and both regularity checks. Thus even the
common-root set need not have cardinality at most 28 from these algebraic
hypotheses alone. No claim is made that U has the required middle support
against a fixed selected received word.

The local three-variable Y/Z weight with weight 28 is
`max(84, degree b)`. For this b it is 84, so the example does not violate the
existing much larger `fixedBranchEvaluationBudget`. It only invalidates
automatic coprimality or a universal 28-root replacement. The generic
reflection proof applies at the actual truncation length 1025; the executable
deliberately checks a small exact length rather than replaying that large
term.

## Valid next interface and unresolved source premise

For a fixed retained factor and a coordinate, construct the two cleared
scalar discrepancies before gamma. On the set where both actual OOD rows
are regular, every support incidence is a root of both. If at least one
discrepancy is nonzero, their common roots have cardinality at most
`natDegree(gcd(D0,D1))`. If both vanish identically, this coordinate is an
identity coordinate, not a root-count event. That is a valid deterministic
interface; it supplies no smaller bound on the gcd's degree.

The missing result would bound these gcd degrees, or control the common
identity coordinates, **using membership in the literal fixed interpolation
parent together with the same actual candidate/support equations**. The
example above is not asserted to occur in that canonical parent. In
particular, choosing a globally zero received word would normally provide
a linear Y factor instead, so that shortcut cannot instantiate this example.

Splitting interpolation across two Taylor centres also does not by itself
halve the budget: clearing two unrelated derivative denominators multiplies
their powers, adding their weighted degrees. With D+1 total Hermite data and
both truncations at least two, the generic exponent sum is `2D-4`, compared
with the one-centre `2D-1`. This is only a constant reduction, not the
roughly sevenfold improvement needed by the current middle-moment target.
Any stronger gain needs shared-denominator cancellation or an additional
source-specific algebraic relation, neither of which is proved here.

## Receipt

No NUC use or Lean build. The focused local command was

```
/usr/bin/time -l sh docs/research/v8-no-work-100-20260907/experiments/run_two_regular_branch_control.sh
```

Its output was retained in `two-regular-branch-control-local-v1.log` through
tee. Observed shell exit zero, all PASS assertions; combined optimized
compilation and execution: 1.33 s wall, 118,439,936 **bytes** peak RSS
(macOS time), zero swaps. rustc 1.93.0, `--edition=2021 -O
-C overflow-checks=yes`, aarch64-apple-darwin. Exact source snapshot and the
post-run executable were retained; no exhaustive selected-field enumeration
or compiler cache build occurred. Research HEAD observed at artifact
completion: `c7dc256f5b4f03cb176ad9059df86b9904886b81`.

SHA256:

* Source and `two-regular-branch-control-local-v1-source.txt`:
  `12daba6a4cb89946c63dd232ab3caa874ba7c7457d8ace59267a4dfe6475a3e1`.
* Runner: `39d3282276147ac0160ba52338025b358cfce0b638f157878cead95c6106ad9e`.
* Log: `780b9b4abcd5d84f99f4e01704435eb94ddb1e707911f3168262fc451aab4a1a`.
* Retained local ignored `target/TwoRegularBranchControl`:
  `490a0a86869984ff8d8fa5ad2713abc7c7f9dbde58d79e2595891707c8f26bd7`.
  This binary hash was taken after the run/copy, not at execution time.
