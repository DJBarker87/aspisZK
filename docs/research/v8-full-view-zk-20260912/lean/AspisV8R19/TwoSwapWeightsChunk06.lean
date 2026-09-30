/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/
import AspisV8R19.TwoSwapWitnessData
namespace AspisR19.TwoSwapWitness
open RootCertificate HighRepairInvariant ResidualModel AspisV8R17
noncomputable section
theorem weights_chunk6 (which : Fin 3) (i : Fin 16) :
  pointFormula which.val (i.val+96)=pointValues which.val (i.val+96) := by
  fin_cases which <;> fin_cases i <;> decide
#print axioms weights_chunk6
end
end AspisR19.TwoSwapWitness
