# Higher-Y singular rows: exact obstruction and causal target

Source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: read-only source inspection and mathematical derivation, **not a
new Lean theorem**. No NUC compilation or cache mutation was performed.

## The gamma-only shortcut is false

Over a field of characteristic different from 3, take

    H(X)=X(X-1),  F(X,Y,Z)=Y^3-H(X)^3 Z,
    t0=0, t1=1, A0(Z)=A1(Z)=0.

F is irreducible: as a polynomial in Z over K[X,Y] it is primitive
(`gcd(Y^3,H^3)=1`), and linear over K(X,Y). Both actual OOD identities hold,
and both actual derivative curves are the ZERO polynomial. Thus the set of
gamma where both derivative evaluations vanish is the entire challenge set.
F is nevertheless globally separable in Y; its resultant with its
Y-derivative is the nonzero `27 H(X)^6 Z^2`.

For every nonzero cube gamma=c^3, the polynomial `U_gamma(X)=c H(X)` is a
horizontal root and agrees with both answers at the OOD points. In a finite
field of order q congruent to 1 modulo 3 this supplies `(q-1)/3` nonzero
gamma values. The actual QM31 cardinality has this congruence. Small exact
F7 coefficient checks gave gamma values {1,6}: all six c values verified
`(cH)^3-c^3 H^3=0` coefficientwise. This was a tiny arithmetic sanity check,
not formal proof or a verifier fixture.

This falsifies “prime plus two identities implies a nonzero actual
derivative curve,” “global separability implies actual-point regularity,”
and a small gamma-only bound for unqualified horizontal roots. It is NOT a
support-qualified counterexample. A received coordinate polynomial of
degree28, away from H=0, can match these roots only at zeros of its fixed
nonzero degree-at-most84 pullback. The checked
`SupportQualifiedRootIncidence` and `CubicSupportControl` explain why such
root-only examples cannot be promoted to many actual qualifying candidates.

## Strongest bounded next target: construct the obstruction, do not assume it

Fix one actual prime factor F of the pre-OOD parent. Write d=degY(F),
x=degX(F), W=weight(Z+28Y)(F), with 3<=d<=111. Define

    D_r(Z) = derivativeCurve F t_r A_r,
    T = { gamma in Gamma | D_0(gamma)=0 and D_1(gamma)=0 }.

The precise proposed theorem is:

    exists E_F in K[X], E_F != 0 and deg(E_F) <= (2d-1)*x,
      for ALL points t_r and polynomial answers A_r of degree <=28,
      if pointSubstitution t_r A_r F=0 for both rows, then
        (E_F(t0)=0 and E_F(t1)=0) OR card(T) <= W-28.

E_F is chosen BEFORE points, answers, gamma or any candidate Q. No supplied
full-resultant-at-point certificate, formal root or candidate curve appears
in the hypotheses. Gamma may be any fixed finite set. Q and all later
responses may be arbitrary: the conclusion bounds a larger event depending
only on the completed OOD prefix. The exceptional OOD event must remain
visible; the cubic above shows why deleting it is invalid.

### Exact proof using existing V7 machinery

1. Existing `exactV7_curvePrimeFactor_derivative_ne_zero`, using the actual
   parent Y-degree bound, gives F_Y!=0. Existing
   `V7ExactCorrelatedAgreementSmooth.separabilityCertificate_ne_zero` then
   DERIVES nonzero Delta_F=Res_Y(F,F_Y), by primitivity and fraction-field
   separability. No characteristic-zero assumption is used.
2. View Delta_F in K[X][Z] and choose any nonzero Z-coefficient E_F(X).
   `coeff_natDegree_le_bivariate_swap_natDegree` and
   `separabilityCertificate_xNatDegree_le` give
   deg E_F <= (d+degY F_Y)*x <= (2d-1)*x. Selection is purely pre-OOD.
3. If a whole identity `F(t,A(Z),Z)=0` also has `D(Z)=0`, then the two
   specialized Y-polynomials share the root A(Z), so their bounded-degree
   resultant is zero. Consequently Delta_F(t,Z)=0 and E_F(t)=0.
   **Missing small adapter:** apply the existing
   `resultant_eq_zero_of_common_root_of_natDegree_le` over K(Z), map the
   root A and the two polynomials into that field, and pull the resultant
   zero back by injectivity. `specialized_resultant_eq_certificate_eval_x`
   supplies the literal identity. This avoids field enumeration and handles
   specialization degree drops without assuming preserved leading degree.
4. Therefore E_F(t_r)!=0 implies D_r is a nonzero polynomial. A coefficient
   proof gives deg D_r <= W-28: differentiate in Y, removing one complete
   weight28, then substitute the degree28 actual answer. This generic
   factor-weight derivative adapter is still needed; the checked parent
   `CurveOODDerivative.selected_degree` must not be mislabeled as a theorem
   about every individual prime factor.
5. If not both E_F(t_r) vanish, choose one such row BEFORE gamma. T is
   contained in its derivative roots, so ordinary polynomial root counting
   gives card(T)<=W-28. This uses the actual derivative curve, not the much
   larger degree of the resultant in Z.

The two missing adapters in steps3-4, followed by a short fixed-factor
wrapper, are a bounded next formalization. Existing `MonicOODBranch` can
then consume the complementary regular gammas. A nonzero full resultant at
the ACTUAL point is never asserted as an external premise.

## Additive actual-family consequence

Take the product E of E_F over the fixed pre-OOD higher-factor submultiset.
Repeated factors are counted with their existing multiplicities. The
already checked additive bounds `MonicFactorOOD.all_factor_x_degrees_le`
and `FactorIdentityCover.all_factor_weights_le`, with the actual selected
parent bounds, imply

    deg E <= 221 * 114687 = 25345827.

Outside `E(t0)=E(t1)=0`, there is ONE common actual row r where E(t_r)!=0;
then E_F(t_r)!=0 for EVERY factor. Among the factors retained by the
completed OOD prefix, multiply their nonzero D_r(Z). This second product is
fixed before gamma. For a nonempty retained higher family its degree is

    sum_F (W_F-28) <= 117077-28 = 117049.

Thus the union of the both-singular gamma events is bounded by 117049,
without a 111-fold multiplier. The empty family contributes zero. Combined
with any eventual regular-branch proof, the proposed higher-factor bound
has the form

    fixed pre-OOD pair-root event + regular mass + 117049/card(Gamma).

The last term alone displays 107.1632469 bits for ideal uniform nonzero
QM31 gamma. This is exact numerator arithmetic, not a newly proved sampler
or accepted-mass theorem. The old 117077 identity-factor-cover charge stays
separate and is not silently replaced; overlapping errors should be combined
by an explicit event decomposition rather than relabeling them.

## Scope and stop

On the bad fixed OOD event the derivative test has no standalone useful
gamma bound. Support-qualified control might still reduce that event, but
the root-only example does not settle it either way. Discharging its actual
probability requires the existing two-point root-set/source coupling work;
do not substitute an existential smooth point for an actual OOD point or
assume Fiat-Shamir freshness.

The helper is still degree2 only at the established source coordinates;
the full received/claim curve here is degree28. C1 remains fixed early,
C2 and the parent are fixed before OOD, both answers before gamma, and Q may
be selected post-alpha. No candidate curve or early decoder success is
assumed. The proposed next proof is the constructed fixed-factor dichotomy
above, not a claim that the singular support-qualified frontier is closed.
