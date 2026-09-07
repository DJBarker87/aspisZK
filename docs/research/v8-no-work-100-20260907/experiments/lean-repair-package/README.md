# A Lean-oriented repair target for the cffcc740 counterexample

Reviewed snapshot: `cffcc740716f220435bd9a5da05b8fc349c8d3e7` in
`DJBarker87/aspisZK`, particularly `decision.md` and
`experiments/JointBoundaryArithmetic.lean` under
`docs/research/v8-no-work-100-20260907/`.

This package does NOT claim a new kernel-checked theorem. Lean/lake are not
installed in the analysis environment. The attached Python tests were run. They
check exact arithmetic and finite algebraic models, not the production verifier,
Fiat–Shamir scheduler, adaptive extractor, privacy or CU. No repository changes
were made. The original fixed-target lemma is already in the reviewed report;
this note makes its implication for the specific counterexample explicit.

## 1. What can and cannot be repaired

The unconditional same-support recovery statement with a 2,800-gamma cap is
false for the reported construction. More formalisation cannot validate that
statement under unchanged hypotheses. The original fixed-family theorem with
its membership assumption is not refuted.

A different security proof can potentially bound the intersection of an
acceptance event and failure of an extractor, instead of treating every failure
of full-support intermediate recovery as a complete security loss. That is a
mathematical change to the reduction. It need not change the candidate protocol
if it can be established for the existing candidate transcript. It does not,
by itself, establish that the candidate's present CU is acceptable.

## 2. Concrete repair lemma for the reported construction

Let K be QM31, k=|K|=(2^31-1)^4, T=262144, J=9557 and q=22. Fix the malicious
received oracles from the decision and fix the two legal OOD points. Common
fibres have all 29 components zero. Each other fibre has the coefficients of
one nonzero monic degree-28 polynomial R_s in gamma, repeated at all four slots.
The claimed component OOD values and the claimed final256 polynomial are zero.

For this statement only, gamma is uniform on K\{0}, alpha is uniform on K
(including zero), and the q-subset S is uniform and independent of both. This
is an ideal fixed-target experiment, not a claim about a prover-controlled
nonce or the complete Fiat–Shamir distribution.

Let A0 mean all q *pointwise folded query residuals* relative to that zero final
polynomial vanish. Let B mean S contains a non-common fibre, so the zero
component tuple does not agree with all actual queried component values.

Then

    Pr[A0 and B] <= (1-b)*e,
    b = choose(J,q)/choose(T,q),
    e = 28/(k-1) + (1-28/(k-1))*3/k.

Consequently

    Pr[A0] <= b+(1-b)*e.

This gives an explicit zero-component target that is correct on the queried
support except for a small *joint* false-consistency event. It is not recovery
of a valid payment witness, nor recovery on the entire 9558-fibre combined
agreement support. Most importantly it is not coverage of arbitrary adaptive
final polynomials.

### Proof

Condition on S containing a non-common fibre and choose the first such fibre
by a deterministic rule depending only on S. On that fibre the combined value
is R_s(gamma), a nonzero degree-28 polynomial. At most 28 nonzero gammas make
it zero. For every other gamma, division by the four nonzero chord denominators
leaves a nonzero four-slot vector v.

The normalized arity-four circle fold is a polynomial in alpha with coefficients

    c0 = (v0+v1+v2+v3)/4,
    c1 = (v0-v1-v2+v3)/(4y),
    c2 = (v0+v1-v2-v3)/(4x),
    c3 = (v0-v1+v2-v3)/(4xy).

The coefficient map is invertible when x,y,2 are nonzero. Thus nonzero v gives
a nonzero polynomial of degree at most three, which has at most three roots.
All q residuals vanishing implies this selected residual vanishes. Average
first over gamma/alpha and then over S. The probability of S being entirely
common is exactly b. There is no union over T fibres or q queried positions.
The calculation analytically conditions on an independent S; it does NOT
propose publishing queries before the prover's commitments.

For a generic fixed-target lemma the same proof uses one nonzero component
residual polynomial on the selected bad fibre instead of the monic R_s. The
pre-challenge fixed-target requirement remains essential.

### Exact arithmetic, displayed in bits

- Original same-support intermediate failure lower bound: 101.2462242116 bits.
- b: 105.1420996194 bits.
- (1-b)*e: **119.0458036869 bits**.
- b+(1-b)*e: **105.1420054893 bits**.

The first quantity is a lower bound on a DIFFERENT event; it is not replaced
by the new upper bound in the old proof. The new theorem must instead connect
the appropriate joint event to the extraction/acceptance experiment.

If the actual query test is one powers-of-rho batched scalar rather than
pointwise checking, additionally charge its nonzero-residual cancellation.
Under a fresh uniform nonzero rho, with residuals fixed before rho, a generic
extra term is (q-1)/(k-1). This yields 105.1419417273 bits for this example's
query-check screen. The actual rho/source event still requires its own proof.
Adding the historical semantic numerator gives a familiar approximately
104.2667-bit number; this is NOT a complete protocol theorem, and the script
labels that hypothetical screen accordingly.

## 3. A second direct algebraic check: folding an inverse chord

This is an auxiliary identity for the specific example, not necessary for the
stronger fixed-target bound above. Write the chord as L=a+bx+cy, x^2+y^2=1.
For the four sign slots, let C_x(alpha) be their normalized fold of 1/L. Clearing
its nonzero denominator gives

    C_x(alpha) = (U(alpha)+x^2*V(alpha))/D_x,
    D_x = ((a+bx)^2-c^2*y^2)*((a-bx)^2-c^2*y^2),
    U(t) = a*(a^2-c^2)-c*(a^2-c^2)*t
           -b*(a^2+c^2)*t^2+2*a*b*c*t^3,
    V(t) = a*(c^2-b^2)-c*(b^2+c^2)*t+b*(b^2+c^2)*t^2.

A chord through two distinct finite circle points has b^2+c^2 nonzero: after
passing to a quadratic extension with i^2=-1, an isotropic chord would have
at most one nonzero root in z=x+i*y. Thus V is nonzero of degree at most two:
if b is nonzero its quadratic coefficient is nonzero; otherwise its linear
coefficient is -c^3, nonzero.

Outside at most two exceptional alphas, distinct fibres have distinct x^2,
so at most one fibre has an accidental reciprocal-fold zero. The disjoint
root intervals give at most one additional R_s(gamma)=0 fibre. Thus at most
J+2 fibres vanish outside the exceptional-alpha set. Another valid example-only
upper bound is

    2/k + (1-2/k)*choose(J+2,q)/choose(T,q),

about 105.13544 bits. It is slightly looser than the fixed-target bound, but
independently checks the geometry behind all folded cancellations, not merely
the all-zero-before-folding subevent. It still fixes the final polynomial to zero.

## 4. What to prove next in Lean

See `LEAN_WORK_ORDER.md`. The central unsolved problem is adaptive coverage of
all accepting continuations, including those on which the partial provider
returns none. A successful theorem about only the provider's Some cases is
not progress on that coverage obligation. A pre-challenge target or a charged
cover must actually be constructed; it cannot be supplied by a membership premise.

## 5. Executed tests

Run:

    python3 check_query_support.py > results.json

Python standard library only. Exact checks over F17, F29, F43 and F59 use actual
circle sign-orbits, nonzero chord denominators, literal four-slot folds, disjoint
polynomial root intervals and all gamma/alpha pairs. Alpha includes zero.

Results: 90 profiles; 6,246 literal reciprocal-fold identity checks;
149,856 gamma/alpha/profile enumerations; 2,250 per-bad-schedule root-bound
checks. The toy fields test the algebraic counting lemma, not secure OOD sampling
in the actual QM31 protocol. No frequency estimate is used to infer a 2^-100 bound.

The elementary algebraic derivation above is universal under its stated
hypotheses; finite tests serve as implementation falsifiers, not a formal proof.
