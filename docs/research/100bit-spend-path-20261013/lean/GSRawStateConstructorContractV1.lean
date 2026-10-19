import GSRawStateCoefficientBridgeV6

set_option autoImplicit false

open Polynomial CompPoly

namespace AspisR1.GSRawStateCoefficientBridge

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

theorem toPoly_ne_zero_of_ne_zero (Q : CBivariate K) (hQ : Q ≠ 0) :
    CBivariate.toPoly Q ≠ 0 := by
  intro hpoly
  apply hQ
  apply CBivariate.eq_iff_coeff.mpr
  intro i j
  have hcoeff := congrArg (fun p : (K[X])[X] => (p.coeff j).coeff i) hpoly
  rw [CBivariate.coeff_toPoly] at hcoeff
  exact hcoeff

/-- Weighted degree plus a coefficient window supplies the full raw-state
constructor contract: exact polynomial model, row degree bound, and nonzeroness.
The row array is the executable inner-X-major representation. -/
theorem gsState_contract
    (Q : CBivariate K) (D maxY d : Nat)
    (hdegree : Q.natWeightedDegree 1 d ≤ D)
    (hwindow : D < d * (maxY + 1)) :
    AspisR1.RRConcreteState.model (gsState Q D maxY) = CBivariate.toPoly Q ∧
    (∀ i ≤ D,
      (RRVectorRowPolynomialBridge.inputPolynomial (gsRows Q D maxY) i).natDegree ≤ maxY) ∧
    (Q ≠ 0 → AspisR1.RRConcreteState.model (gsState Q D maxY) ≠ 0) := by
  obtain ⟨hX, hY⟩ := coefficient_window_of_weightedDegree Q d D maxY hdegree hwindow
  have hmodel := gsState_model_eq Q D maxY hY hX
  refine ⟨hmodel, ?_, ?_⟩
  · intro i hi
    rw [inputPolynomial_eq_slice Q D maxY i (hY i) hi]
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [RRActualBivariateTaylorBridge.xCoeffSlice_coeff, CBivariate.coeff_toPoly]
    exact hY i j hj
  · intro hQ
    rw [hmodel]
    exact toPoly_ne_zero_of_ne_zero Q hQ

#print axioms toPoly_ne_zero_of_ne_zero
#print axioms gsState_contract

end AspisR1.GSRawStateCoefficientBridge
