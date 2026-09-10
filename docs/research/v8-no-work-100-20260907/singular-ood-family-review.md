# Additive higher-factor singular cover

Status: **kernel-checked**. New sources are
[SingularOODFamily.lean](experiments/SingularOODFamily.lean) and its small
dependent [SelectedSingularOODFamily.lean](experiments/SelectedSingularOODFamily.lean).
The generic predecessor and then the selected adapter compiled as focused
cached leaves. Their nine audits contain only `propext`, `Classical.choice`,
and `Quot.sound`; there is no `sorry` or new axiom.

## Fixed sets and exact causal order

Let H(P) be `curvePrimeFactors P` filtered by degY>=3. This is a **multiset**,
fixed with the actual C1/C2 parent before either OOD point. Define

    E(P) = product over F in H(P) of SingularOODCoefficient.obstruction F.

Do not instead form E from only the factors retained after OOD: that would
lose its pre-OOD fixing. Repeated prime factors are kept in H(P), both
products, and both budget sums. No disjointness or factor-count union is
assumed.

After the two arbitrary sequential points and degree28 answer curves are
fixed, if not both points are roots of E, choose one common row r where
E(t_r)!=0. Every factor obstruction is nonzero at that same row. Filter H(P)
by the actual two-identity `Retained` predicate, then multiply that row's
literal `derivativeCurve` polynomials to form Z. These derivative polynomials
are individually nonzero by the checked source/resultant bridge, so Z!=0.
Z is fixed before gamma, without fixing any candidate or final.

Every gamma with **any** retained higher factor singular at both rows is a
root of Z. Thus the bound covers all later adaptive factor/candidate choices
at once. The polynomial cover is returned for all gamma, before a finite
challenge set is supplied to the counting corollary.

## Additive budgets and empty families

`MonicFactorOOD.all_factor_x_degrees_le` and the per-factor coefficient bound
give

    deg E <= (2 degY P-1) * degX P.

The retained derivative product has degree at most

    sum_retained (W_F-28) <= sum_retained W_F-28 <= W_P-28.

The first inequality uses W_F>=28 for positive-Y factors, derived from the
leading coefficient's weighted degree. All subtraction is natural-number
subtraction. The empty family is not a missing case: both products are1,
the sum/degree is0, and there are no singular witnesses. No unsupported
nonempty-family premise is introduced.

`FactorIdentityCover.all_factor_weights_le` supplies the true additive parent
budget. We do not multiply the gamma bound by111. Keeping each repeated
factor only overcounts roots, while its repeated degree is already paid.

For the actual selected parent, the existing source theorems give

    degY P <=111,  degX P <=114687,  W_P <=117077.

The selected draft derives—not assumes—the corresponding numeric result:

    E !=0, deg E <=221*114687 =25345827,
    both actual OOD points are E-roots
      OR |simultaneously singular gamma union| <=117049.

It uses `SelectedLinearCover.parent_y_degree`,
`SelectedMonicCover.parent_x_degree`, and the V7 coefficient-form
`trivariateYZWeight_curveTrivariatePolynomial_lt` theorem. The final small
adapter substitutes literal `SelectedOODGate.point` and
`CurveOODGate.answerCurve`, using existing `answers_degree`.

## Scope and falsifier

The pair-root alternative stays explicit. The cubic
F=Y^3-[X(X-1)]^3 Z with zero OOD answers at0 and1 still makes both actual
derivative curves identically zero, despite prime/global separability.
This rules out dropping that alternative; it does not supply a selected
support-qualified acceptance counterexample.

The new event has no candidate/support requirement and is deliberately
larger than the actual qualified singular event. There is no assumption
of component-tuple coverage, exact received polynomiality, early C1 decoder
success, or a pre-alpha final. The source helper remains degree2 where its
existing support law applies; the full claim/answer degree here remains28.

These drafts do not combine regular acceptance, the old117077 identity-cover
exception, or any sampler probability. In particular, no independent OOD
labels, Fiat-Shamir freshness, or conditional uniformity is inferred from
the algebra. No whole-source security or payment conclusion is asserted.

Proposed audits: seven generic/family endpoints, then two selected endpoints.
The immutable checked dependencies are `SingularOODCoefficient`,
`SingularOODResultant`, `FactorDerivativeWeight`, `MonicFactorOOD`,
`FactorIdentityCover`, and the selected parent interfaces above. Private
multiset helpers reproduce only elementary sum/product inductions because
the earlier identical helper declarations are private to their modules.

## Focused verification

Generic attempts v1--v4 exposed only elaboration issues around definitional
filter equality and a missing local decidability instance. Those failed logs
are retained. After making the predicate instance explicit and keeping the
symbolic multiset proof unchanged, v5 exited 0 in 3.74 seconds with peak RSS
6,838,652 KiB and zero swaps. The selected adapter then passed on its first
attempt in 3.05 seconds with peak RSS 6,865,160 KiB and zero swaps. Both used
MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%, Lean
4.32.0 and `-j1 -M9500`; the 919- and 921-entry provenance checks passed
before and after each target.

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SingularOODFamily singular-ood-family-nuc-v5
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SelectedSingularOODFamily selected-singular-ood-family-nuc-v1
```

| Artifact | SHA-256 |
| --- | --- |
| Generic source | `d30e4cb3ca6753048fa30a77515027fa2bbd090f5b237ed199bb54d170880ab4` |
| Generic olean | `56cb99a33aa0d6005bb9167549980185203e0ab23c8242ed6780f5683adea253` |
| Generic manifest | `9e28715def0b58ec6e7e28f7a637fe501d6cf7b652a3a68f7d9045812f0ca7f2` |
| Generic log | `ba21e4c01f7da98fb7491f15632f7bf2c741aa51e6e0d3a923a2facd33dff998` |
| Selected source | `5e19bbc376221bc8ba1ee18416c55426e1d4d18c2fd77dd6d58105c1654a1ffe` |
| Selected olean | `9f65ee44e7ac0fbcaa71c01ed25fafeb4e8f647adf0c58a27035341f87b762f1` |
| Selected manifest | `8e6bec8a8c959ae9a38906ca87e305415ab1405b66e7af510092d65c2f486370` |
| Selected log | `5671b7f7680b3a246e50d033d2d273c3a405b7107444aa02138bc95c8c387ab1` |
