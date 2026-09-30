/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/
import AspisV8R19.TwoSwapWitnessData
namespace AspisR19.TwoSwapWitness
open RootCertificate HighRepairInvariant ResidualModel AspisV8R17
noncomputable section
theorem inverse_row3 (j : Fin 13) : (expectedMatrix*inverseMatrix) 3 j=(1:Matrix (Fin 13) (Fin 13) M) 3 j := by
  fin_cases j <;> (rw [Matrix.mul_apply]; decide)
#print axioms inverse_row3
end
end AspisR19.TwoSwapWitness
