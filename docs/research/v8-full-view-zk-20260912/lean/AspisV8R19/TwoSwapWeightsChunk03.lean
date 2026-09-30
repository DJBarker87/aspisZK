/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/
import AspisV8R19.TwoSwapWitnessData
namespace AspisR19.TwoSwapWitness
open RootCertificate HighRepairInvariant ResidualModel AspisV8R17
noncomputable section
theorem weights_chunk3 (which : Fin 3) (i : Fin 16) :
  pointFormula which.val (i.val+48)=pointValues which.val (i.val+48) := by
  fin_cases which <;> fin_cases i <;> decide
#print axioms weights_chunk3
end
end AspisR19.TwoSwapWitness
