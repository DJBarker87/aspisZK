import AspisV8R16.NaturalCoverage
import AspisV8R16.TransportDual
import AspisV8R17.RawFinalCoverage
import AspisV8R18.SparseCoordinates
import AspisV8R19.R541JointSchurEquivalence
import AspisV8R19.R588NormalizedCoreDomainBound
import AspisV8R19.R686AllBetaJointGCorrection
import AspisV8R19.R714SelectedActiveNonzero
import AspisV8R19.R727TopBalance
import AspisV8R19.R885CompleteSemanticGridBound
import AspisV8R19.R941BalancedSource223Repair
import AspisV8R19.TwoSwapFixedRootProbability

/-!
V8 audit 2026-10-05, Phase 1: algebraic privacy nodes that are discharged by a
theorem already in the tree at 4e0f47381.  Statements only; every proof term is
the name of an existing theorem.  No new lemma is proved in this file.

A node written with `type_of%` has, as its statement, exactly the statement of
the named theorem at universe 0.  Its docstring is the two-sentence reading.
-/
set_option autoImplicit false
namespace V8Audit.Privacy
open scoped BigOperators

/-- P20. The R16 basis transport `T` has a two-sided inverse on all of `F^I`:
`T (T⁻¹ c) = c` for every coefficient vector `c`, with no legality premise. -/
def Node_P20 : Prop :=
  ∀ {ι F : Type} [DecidableEq ι] [AddCommGroup F] (inactive : Finset ι) (pivot : ι),
    pivot ∈ inactive → ∀ (order : ι ≃ ι) (c : ι → F),
      AspisV8R16.transport inactive pivot order
        (AspisV8R16.inverseTransport inactive pivot order c) = c
theorem node_P20 : Node_P20 :=
  fun inactive pivot hp order c => AspisV8R16.transport_inverse inactive pivot hp order c

/-- P21. Verifier weights transport through `T` by the explicit dual: for every
`w` and `c`, `⟨w, T⁻¹ c⟩ = ⟨T* w, c⟩`. -/
def Node_P21 : Prop := type_of% @AspisV8R16.inverseTransport_dot.{0, 0}
theorem node_P21 : Node_P21 := @AspisV8R16.inverseTransport_dot.{0, 0}

/-- P22. For any `n` distinct fold coordinates, the first `n` natural-basis
coefficients in each of the four slot channels realise arbitrary values at all
`4n` raw opening positions (raw coverage for every injective schedule). -/
def Node_P22 : Prop := type_of% @AspisV8R16.natural_four_slot_coverage.{0}
theorem node_P22 : Node_P22 := @AspisV8R16.natural_four_slot_coverage.{0}

/-- P23. Raw values at `n` distinct roots and a prescribed final polynomial of
degree `< m` are simultaneously realisable whenever they agree under the
four-point fold at every root. -/
def Node_P23 : Prop := type_of% @AspisV8R17.compatible_raw_final_coverage.{0}
theorem node_P23 : Node_P23 := @AspisV8R17.compatible_raw_final_coverage.{0}

/-- P24. The sparse-G slot map `i ↦ 128 + 3 i` selects exactly 271 of the 1023
non-pivot code coordinates. -/
def Node_P24 : Prop := AspisV8R18.selected.card = 271
theorem node_P24 : Node_P24 := AspisV8R18.selected_card

/-- P25. H1 active-core image.  If the selected active determinant is nonzero
at `(alpha, u, v0)`, every target on the 214 copy-active rows is met by a
quotient vector that vanishes at all 22 query roots, has zero first fold, zero
top four coefficients and zero inactive balance. -/
def Node_P25 : Prop := type_of% @AspisV8R19.R727TopBalance.balanced_query_active_core_image.{0}
theorem node_P25 : Node_P25 := @AspisV8R19.R727TopBalance.balanced_query_active_core_image.{0}

/-- P26. Over uniform `(alpha, u, v0) ∈ QM31³` the selected active determinant
vanishes with probability at most `1070 / p⁴`. -/
def Node_P26 : Prop :=
  type_of% @AspisV8R19.R714SelectedActiveNonzero.product_domain_bad_fraction_explicit
theorem node_P26 : Node_P26 :=
  @AspisV8R19.R714SelectedActiveNonzero.product_domain_bad_fraction_explicit

/-- P27. Full-223 ordinary repair (R941).  For an ordinary quotient vector with
zero first fold, `q₁₀₂₃ = 0`, `b·q₁₀₂₂ − c·q₁₀₂₁ = 0` and zero inactive balance,
and a nonzero normalised 223 determinant, a combination of the 223 selected
directions matches all 214 active rows, three point rows, seven relation
coefficients and an arbitrary semantic pairing target while vanishing at the
22 query roots and keeping fold, tail and balance zero. -/
def Node_P27 : Prop :=
  type_of% @AspisV8R19.R941BalancedSource223Repair.balanced_source_compatible_223_repair.{0}
theorem node_P27 : Node_P27 :=
  @AspisV8R19.R941BalancedSource223Repair.balanced_source_compatible_223_repair.{0}

/-- P28. For every fixed legal 22-root tuple, the selected 223 determinant
vanishes on at most a `14049 / m` fraction of any 15-coordinate product grid
whose sides have at least `m` elements. -/
def Node_P28 : Prop :=
  type_of% @AspisV8R19.R885CompleteSemanticGridBound.selected_root_grid_bound
theorem node_P28 : Node_P28 :=
  @AspisV8R19.R885CompleteSemanticGridBound.selected_root_grid_bound

/-- P29. Joint G correction for every beta (R686).  With nonzero core and
residual determinants, a fold-free ordinary residual whose seven plain relation
coefficients and structured moment vanish admits a G change realising any
271-coin target of zero finish-moment, with zero point rows and query roots. -/
def Node_P29 : Prop :=
  type_of% @AspisV8R19.R686AllBetaJointGCorrection.all_beta_joint_g_correction.{0}
theorem node_P29 : Node_P29 :=
  @AspisV8R19.R686AllBetaJointGCorrection.all_beta_joint_g_correction.{0}

/-- P30. For every fixed legal 22-root tuple, the two-swap G-residual 13×13
determinant vanishes on at most `819 / p⁴` of product-uniform QM31 assignments
of its 36 challenge coordinates. -/
def Node_P30 : Prop :=
  type_of% @AspisR19.TwoSwapFixedRootProbability.bad_fraction_le_explicit
theorem node_P30 : Node_P30 :=
  @AspisR19.TwoSwapFixedRootProbability.bad_fraction_le_explicit

/-- P31. The normalised sparse-G core determinant vanishes on at most a
`1355 / m` fraction of any three-coordinate product grid of side at least `m`. -/
def Node_P31 : Prop :=
  type_of% @AspisV8R19.R588NormalizedCoreDomainBound.normalizedDet_domain_fraction_bound
theorem node_P31 : Node_P31 :=
  @AspisV8R19.R588NormalizedCoreDomainBound.normalizedDet_domain_fraction_bound

/-- P32. The marker contraction of a quotient vector equals the inactive-row
sum of its inverse-transported mask, over any commutative ring. -/
def Node_P32 : Prop :=
  type_of% @AspisV8R19.R940MarkerBalance.marker_pairing_eq_inactive_balance.{0}
theorem node_P32 : Node_P32 :=
  @AspisV8R19.R940MarkerBalance.marker_pairing_eq_inactive_balance.{0}

/-- P33. Joint H1/G criterion.  Given a complete parametrisation of the H1
kernel and of the G image, a joint affine correction exists exactly when the
finite obstruction system is solvable. -/
def Node_P33 : Prop := type_of% @AspisV8R19.R541.joint_schur_equivalence.{0, 0, 0, 0, 0, 0, 0}
theorem node_P33 : Node_P33 := @AspisV8R19.R541.joint_schur_equivalence.{0, 0, 0, 0, 0, 0, 0}

#print axioms node_P20
#print axioms node_P21
#print axioms node_P22
#print axioms node_P23
#print axioms node_P24
#print axioms node_P25
#print axioms node_P26
#print axioms node_P27
#print axioms node_P28
#print axioms node_P29
#print axioms node_P30
#print axioms node_P31
#print axioms node_P32
#print axioms node_P33
end V8Audit.Privacy
