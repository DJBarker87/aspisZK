# Fixed pre-OOD resultant coefficient

Source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: kernel-checked. The first focused NUC compilation of
[SingularOODCoefficient.lean](experiments/SingularOODCoefficient.lean)
passed, and all eight axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorry` or new axiom.

## Exact proposed endpoint

For one prime factor F of the fixed pre-OOD parent P, let d=degY F>0 and
x=degX F. Define, with the actual nested V7 variable order,

    Delta_F = Res_Y(F, derivative_Y F) in K[X][Z],
    E_F = leadingCoeff_Z(Delta_F) in K[X].

`exactV7_obstruction_control` derives E_F != 0 from prime membership,
P != 0 and degY P < 113. It gives deg E_F <= (2d-1)x. The SAME E_F is then
used universally for all actual points t_0,t_1, answers A_0,A_1 of degree
at most28, and finite Gamma. If both literal OOD polynomial identities
F(t_r,A_r(Z),Z)=0 hold, the conclusion is

    [E_F(t_0)=0 and E_F(t_1)=0]
      OR
    |{gamma in Gamma : D_0(gamma)=D_1(gamma)=0}| <= W_F-28,

where D_r is the actual derivativeCurve and W_F is the actual trivariate
weight Z+28Y. Natural subtraction also covers vacuous small-weight cases
in the generic lemma. The selected positive-Y factors have sufficient
weight automatically. The generic theorem is stated at arbitrary answer
degree c, then specialized to28; it never substitutes helper degree2.

The result deliberately bounds a larger event without any candidate,
support, received-polynomial, original-code, final, or query premise. Thus
post-alpha adaptive Q/finals do not cause a fixing problem. E_F depends
only on F; a nonzero derivative row is selected after the completed OOD
prefix and before gamma. No independent-point or uniform-gamma sampler law
is asserted.

## Reused proof dependencies

- `V7ExactCorrelatedAgreementFactors.exactV7_curvePrimeFactor_derivative_ne_zero`
  uses the actual QM31 characteristic and the parent's degree bound, not
  characteristic-zero intuition or an assumed nonzero derivative.
- `V7ExactCorrelatedAgreementSmooth.separabilityCertificate_ne_zero`
  derives Delta_F != 0 by the prime factor's primitivity, fraction-field
  Gauss bridge, and separability.
- That module's `coeff_natDegree_le_bivariate_swap_natDegree` and
  `separabilityCertificate_xNatDegree_le`, followed by Mathlib's
  `natDegree_derivative_le`, give the X-degree budget.
- `FactorIdentityCover.coeff_swap_eval` derives the literal coefficient
  transport, including the swap direction. A whole actual OOD identity
  plus whole derivative identity implies Delta_F(t,Z)=0 by the already
  checked `SingularOODResultant.source_singular_certificate`, which covers
  specialization degree drops and zero specialized polynomials.
- `FactorDerivativeWeight.derivative_curve_degree` gives W_F-c. Standard
  polynomial root counting bounds the simultaneous event by either
  nonzero actual derivative curve. No resultant Z-degree is charged.

The new leaf imports only `SingularOODResultant` and `FactorDerivativeWeight`;
their existing checked dependencies provide the reused V7 interfaces.
Eight explicit axiom audits are proposed. No selected encoder or large
finite-domain expansion is needed.

## Necessary exception and remaining work

The already recorded cubic F=Y^3-[X(X-1)]^3 Z, with t_0=0,t_1=1 and zero
answers, is prime and globally separable in characteristic different
from3. Its nonzero resultant is 27[X(X-1)]^6 Z^2, so E_F vanishes at both
actual points and both derivative curves are identically zero. Many cube
gammas have compatible horizontal polynomial roots. This falsifies
deleting the E_F pair-root alternative or replacing actual-point regularity
with global separability. It is a root-only falsifier, not a counterexample
to selected support-qualified acceptance; see
[the scoped singular-row analysis](higher-y-singular-row-plan.md).

Additive factor-family composition, the actual selected parent degree
instantiation, its accepted-event decomposition, and any probability for
the fixed pair-root event are subsequent work, not supplied premises or
credits of this leaf. The current source adapter retains the original
full degree28 claims and places no restriction on the degree2 helper curve
or adaptive final strategy.

## Focused verification

The first focused attempt was green. It exited 0 in 4.22 seconds with peak
RSS 6,797,568 KiB and zero swaps under MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%, Lean 4.32.0 and
`-j1 -M9500`. Both 915-entry provenance checks passed; no dependency or
unchanged package-wide proof suite was replayed.

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SingularOODCoefficient singular-ood-coefficient-nuc-v1
```

- Source SHA256:
  `e4bd6c016ea792946d3e1429ccc7a3a4dde1744813dc53a5ab00dc59e29f51a1`.
- Olean SHA256:
  `12594ca5151a48e352d954ab3a6174fdbf33e6e30e8156572c1bef78eda1d84b`.
- Manifest SHA256:
  `2515f4404f06123db90ebaa54d6353c3b0917b70df71f2f7a3d28d11bcbaa76e`.
- Log SHA256:
  `3a30b3f6a38e62230490b46ed598e81ad7a9bdc9575613824ed9eb786d0336e6`.
