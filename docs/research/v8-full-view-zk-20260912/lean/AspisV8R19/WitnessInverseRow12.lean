/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessInverseData
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem inverse_row12 (j : Fin 13) : (matrix*inverseMatrix) 12 j = (1:Matrix (Fin 13) (Fin 13) M) 12 j := by
  fin_cases j <;> (rw [Matrix.mul_apply]; decide)
#print axioms inverse_row12
end
end AspisR19.WitnessEntryData
