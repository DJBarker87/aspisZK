/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessInverseData
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem inverse_row11 (j : Fin 13) : (matrix*inverseMatrix) 11 j = (1:Matrix (Fin 13) (Fin 13) M) 11 j := by
  fin_cases j <;> (rw [Matrix.mul_apply]; decide)
#print axioms inverse_row11
end
end AspisR19.WitnessEntryData
