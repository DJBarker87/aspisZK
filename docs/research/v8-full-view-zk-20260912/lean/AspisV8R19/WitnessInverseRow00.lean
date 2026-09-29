/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessInverseData
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem inverse_row0 (j : Fin 13) : (matrix*inverseMatrix) 0 j = (1:Matrix (Fin 13) (Fin 13) M) 0 j := by
  fin_cases j <;> (rw [Matrix.mul_apply]; decide)
#print axioms inverse_row0
end
end AspisR19.WitnessEntryData
