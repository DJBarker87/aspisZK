/- Generated fixed high-coordinate certificate. No query recurrence is evaluated. -/
import AspisV8R19.HighWitnessData
namespace AspisR19.HighWitnessData
open RootCertificate
noncomputable section
theorem inverse_row12 (j : Fin 13) : (expectedMatrix*inverseMatrix) 12 j = (1:Matrix (Fin 13) (Fin 13) M) 12 j := by
  fin_cases j <;> (rw [Matrix.mul_apply]; decide)
#print axioms inverse_row12
end
end AspisR19.HighWitnessData
