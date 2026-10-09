# Singular OOD resultant

Source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: `SingularOODResultant.lean` is kernel-checked on the capped NUC
runner. Its two audits contain only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorry` or new axiom.

The source-shaped target is exactly:

    pointSubstitution t A F = 0
    derivativeCurve F t A = 0
    0 < degreeY(F)
      ⇒ (swap (separabilityCertificate F)).eval (C t) = 0.

Both premises are whole polynomial identities in gamma. The conclusion
concerns the SAME actual OOD point and answer. It is not inferred from a
single gamma value, does not replace the point with an existential smooth
one, and requires no horizontal candidate or supplied resultant certificate.
Apply it separately at the two actual rows when both derivative curves are
identically zero. Primeness, answer degree and characteristic bounds are
not needed for this zero implication; they belong to other stages.

## Generic predecessor and degree drops

`common_root_resultant_zero` is over an arbitrary coefficient integral
domain R. It maps the two polynomials and their common root into
`FractionRing R`, invokes the EXISTING V7
`resultant_eq_zero_of_common_root_of_natDegree_le`, and pulls the resultant
zero back using the injective coefficient map and `resultant_map_map`.
For the source corollary, R is K[Z] and its fraction field is K(Z).

The supplied resultant sizes remain F.natDegree and
F.derivative.natDegree. Specializing X can reduce either actual degree or
make either polynomial zero: only upper bounds are used. No leading
coefficient preservation is assumed. The adapter does not replace the
resultant by one silently resized after specialization.

The positive first size is necessary. For two zero polynomials with both
sizes zero, the Sylvester matrix is 0-by-0 and its determinant is one,
although every scalar is a common root. With positive first size the old
theorem includes this degenerate polynomial case. A nonzero degree-dropping
specialization is handled by the same existing upper-bound theorem.

Only `FactorCoherence` and the already-used native
`Mathlib.RingTheory.Localization.FractionRing` are imported. Root mapping
uses `eval_map`/`eval₂_at_apply`; degree bounds use `natDegree_map_le`; the
actual certificate map is existing
`specialized_resultant_eq_certificate_eval_x`. No UFD/resultant proof is
duplicated, no field/domain enumeration occurs, and no limits are raised.

## What this supplies next

For a fixed prime factor with derived nonzero global resultant, choose a
nonzero Z-coefficient E_F(X) before OOD. This adapter proves that an actual
answer identity with an identically singular derivative forces E_F(t)=0.
Consequently E_F(t)!=0 forces that actual derivative curve to be nonzero;
the now-checked `FactorDerivativeWeight` can bound its finite gamma roots.

Coefficient selection, its pre-OOD degree budget, factor-family union and
accepted-mass/actual-sampler composition remain separate. This draft must
not be confused with those later steps.

## Focused verification

The first focused attempt was green: exit0 in3.80s, peak RSS6,781,092KiB,
zero swaps, MemoryHigh8GiB/MemoryMax10GiB/SwapMax0/CPU200%, Lean4.32.0,
`-j1 -M9500`. Both 907-entry provenance checks passed.

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SingularOODResultant singular-ood-resultant-nuc-v1
```

- Source SHA256:
  `fc5f4cb3033de5c13ecdb8bbcc073ced65fc386b7f677f5b5e7a2e8d59187ab4`.
- Olean SHA256:
  `c590d85e230b2a3723f52bd9b8536047107bb1e39c27866327a0091575efc5fe`.
- Manifest SHA256:
  `f593cba88a75c059484ae5a7ed54536f5c238084b324602e1a455e8237612ed1`.
- Log SHA256:
  `3942abaa28c46f296b3348a67f0a7d48a7d3a637e841b3bce3aba6931ed7fe8d`.
