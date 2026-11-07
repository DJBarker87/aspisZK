import NNH_LaneModel
import NNH_MappedOk
set_option autoImplicit false
noncomputable section
namespace NNH_LaneOk
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier

theorem value (b : Slice U8) (lane : RSL.LaneState)
 (success : NND_LaneReturned.value (bytes b)=.ok lane) :
 ∃ n,NNH_LaneModel.decode b=.ok (.Ok n) ∧ NND_Carrier.lane n=lane := by
 have mapped := NNH_LaneModel.mapped b
 rw [success] at mapped
 exact NNH_MappedOk.value _ _ _ mapped
#print axioms value
end NNH_LaneOk
