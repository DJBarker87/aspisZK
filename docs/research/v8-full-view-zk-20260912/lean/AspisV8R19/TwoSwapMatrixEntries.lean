/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/
import AspisV8R19.TwoSwapWitnessData
namespace AspisR19.TwoSwapWitness
open RootCertificate HighRepairInvariant ResidualModel AspisV8R17
noncomputable section
theorem matrix_entries : matrix=expectedMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide
#print axioms matrix_entries
end
end AspisR19.TwoSwapWitness
