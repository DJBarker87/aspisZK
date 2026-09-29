/- Generated staged point-weight certificate. Do not inline earlier stages. -/
import AspisV8R19.WitnessPointData
namespace AspisR19.WitnessPointData
open RootCertificate ResidualModel
noncomputable section
theorem code_preflight : codeWeight ResidualPins.order ResidualPins.inactive coords1 (107:Fin 111) = code1 107 := by decide
theorem sparse_preflight : ∀ j : Fin 111, j ∉ ({105,106,107,109,110}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 107 j.val = 0 := by
  intro j
  fin_cases j <;> decide
theorem weight_preflight : (∑ j : Fin 111, code1 j * chordEntry half (7:M) 5 (-5) 107 j.val) = weights1 107 := by
  rw [PointWeightCertificate.sparse_sum _ _ _ sparse_preflight]
  decide
#print axioms code_preflight
#print axioms sparse_preflight
#print axioms weight_preflight
end
end AspisR19.WitnessPointData
