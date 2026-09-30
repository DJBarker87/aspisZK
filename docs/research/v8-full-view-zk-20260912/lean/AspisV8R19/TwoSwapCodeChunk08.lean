/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/
import AspisV8R19.TwoSwapWitnessData
namespace AspisR19.TwoSwapWitness
open RootCertificate HighRepairInvariant ResidualModel AspisV8R17
noncomputable section
theorem code_chunk8 (which : Fin 3) (i : Fin 3) :
  codeFormula which.val (i.val+128)=codeValues which.val (i.val+128) := by
  fin_cases which <;> fin_cases i <;> decide
#print axioms code_chunk8
end
end AspisR19.TwoSwapWitness
