import R1RoundPairing
import R1FirstFold

/-! Identify the existing coefficient-layer fold with the primal fold used
by the checked round-pairing algebra. This is an algebraic identity, not a
runtime source correspondence result. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.FoldCoefficientBridge

open scoped BigOperators
open AspisV5ComponentCConcreteFoldLinearity

variable {K : Type} [Field K]

theorem coefficientFoldValue_eq_sum (alpha : K) (v : Fin 4 → K) :
    coefficientFoldValue alpha v = ∑ s : Fin 4, alpha ^ s.val * v s := by
  rw [Fin.sum_univ_four]
  simp [coefficientFoldValue]

theorem coefficientFoldLayer_eq_primalFold {n : Nat}
    (alpha : K) (q : Fin (4 * n) → K) :
    coefficientFoldLayer n alpha q = AspisR1.RoundPairing.primalFold alpha q := by
  funext i
  rw [coefficientFoldLayer_apply, coefficientFoldValue_eq_sum]
  unfold AspisR1.RoundPairing.primalFold
  apply Finset.sum_congr rfl
  intro s _
  change alpha ^ s.val * q (AspisR1.childIndex i s) = _
  exact mul_comm _ _

theorem curveValue_eq_coefficientFoldValue
    [Fintype K] [DecidableEq K] {D : Type} [Fintype D] [DecidableEq D]
    (g : Fin 4 → D → K) (alpha : K) (i : D) :
    AspisV5FriDegreeThreeCorrelatedAgreement.curveValue g alpha i =
      coefficientFoldValue alpha (fun s => g s i) := by
  simp only [AspisV5FriDegreeThreeCorrelatedAgreement.curveValue,
    AspisV5FunctionalBatching.batchedDiscrepancy, coefficientFoldValue]
  ring

#print axioms coefficientFoldValue_eq_sum
#print axioms coefficientFoldLayer_eq_primalFold
#print axioms curveValue_eq_coefficientFoldValue
end AspisR1.FoldCoefficientBridge
end
