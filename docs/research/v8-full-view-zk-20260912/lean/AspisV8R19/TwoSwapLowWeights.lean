/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/
import AspisV8R19.TwoSwapWitnessData
namespace AspisR19.TwoSwapWitness
open RootCertificate HighRepairInvariant ResidualModel AspisV8R17
noncomputable section
theorem point_low0 (d : Fin 23) (s : Fin 4) :
    pointValues 0 (4*d.val+s.val)=pointValues 0 s.val := by
  fin_cases d <;> fin_cases s <;> decide
#print axioms point_low0
theorem point_low1 (d : Fin 23) (s : Fin 4) :
    pointValues 1 (4*d.val+s.val)=pointValues 1 s.val := by
  fin_cases d <;> fin_cases s <;> decide
#print axioms point_low1
theorem point_low2 (d : Fin 23) (s : Fin 4) :
    pointValues 2 (4*d.val+s.val)=pointValues 2 s.val := by
  fin_cases d <;> fin_cases s <;> decide
#print axioms point_low2
theorem channel_low0 (d : Fin 23) (s : Fin 4) :
    channelValues 0 (4*d.val+s.val)=channelValues 0 s.val := by
  fin_cases d <;> fin_cases s <;> decide
#print axioms channel_low0
theorem channel_low1 (d : Fin 23) (s : Fin 4) :
    channelValues 1 (4*d.val+s.val)=channelValues 1 s.val := by
  fin_cases d <;> fin_cases s <;> decide
#print axioms channel_low1
end
end AspisR19.TwoSwapWitness
