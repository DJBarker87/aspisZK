/- Generated fixed high-coordinate certificate. No query recurrence is evaluated. -/
import AspisV8R19.HighWitnessData
namespace AspisR19.HighWitnessData
open RootCertificate
noncomputable section
theorem model_matrix : SparseHighWitness.matrix = expectedMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide
#print axioms model_matrix
end
end AspisR19.HighWitnessData
