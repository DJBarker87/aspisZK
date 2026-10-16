import ExtractedMaskHornerPolynomial
import ExtractedMaskTerminalHorner

/-! Relate the already checked loop recurrence to the historical seeded
Horner expression symbolically in the length. No concrete recurrence unfolds. -/
set_option autoImplicit false
namespace AspisR1.TerminalHornerModel
open scoped BigOperators
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

theorem actual_model_eq_seeded (coefficients : Nat → ExactQM)
    (theta seed : ExactQM) (n : Nat) :
    AspisR1.ExtractedMaskHornerLoop.hornerLoopModel coefficients theta n seed =
      AspisR1.ExtractedMaskTerminalHorner.seededHorner theta seed
        (List.ofFn (fun i : Fin n => coefficients i.val)) := by
  rw [AspisR1.ExtractedMaskHornerPolynomial.actual_model_eq_generic,
    AspisR1.ExtractedMaskHornerPolynomial.hornerLoopModel_eq_sum,
    AspisR1.ExtractedMaskTerminalHorner.seededHorner_eq_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun i : Nat => coefficients i * theta ^ i) n]

#print axioms actual_model_eq_seeded
end AspisR1.TerminalHornerModel
