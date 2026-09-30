/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/
import AspisV8R19.TwoSwapWitnessData
namespace AspisR19.TwoSwapWitness
open RootCertificate HighRepairInvariant ResidualModel AspisV8R17
noncomputable section
theorem channel_formula1 (r : Fin 128) :
    channelFormula true r.val=channelValues 1 r.val := by
  fin_cases r <;> decide
#print axioms channel_formula1
end
end AspisR19.TwoSwapWitness
