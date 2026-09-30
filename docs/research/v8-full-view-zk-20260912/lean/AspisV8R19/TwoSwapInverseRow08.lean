/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/
import AspisV8R19.TwoSwapWitnessData
namespace AspisR19.TwoSwapWitness
open RootCertificate HighRepairInvariant ResidualModel AspisV8R17
noncomputable section
theorem inverse_row8 (j : Fin 13) : (expectedMatrix*inverseMatrix) 8 j=(1:Matrix (Fin 13) (Fin 13) M) 8 j := by
  fin_cases j <;> (rw [Matrix.mul_apply]; decide)
#print axioms inverse_row8
end
end AspisR19.TwoSwapWitness
