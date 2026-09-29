/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessInverseData
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem inverse_row2 (j : Fin 13) : (matrix*inverseMatrix) 2 j = (1:Matrix (Fin 13) (Fin 13) M) 2 j := by
  fin_cases j <;> (rw [Matrix.mul_apply]; decide)
#print axioms inverse_row2
end
end AspisR19.WitnessEntryData
