import NND_ZeroCarrier
import NNH_MappedOk
set_option autoImplicit false
namespace NNH_Stage1ZeroOk
open Aeneas Aeneas.Std AdapterRw NND_Carrier

theorem source (data : Slice U8) (zero : RSL.requireZero (bytes data)=.ok ()) :
 r1_pool_adapter.owned.require_zero data=.ok (.Ok ()) := by
 have mapped:=NND_Carrier.historical_zero data
 rw [zero] at mapped
 obtain ⟨unit,native,same⟩ := NNH_MappedOk.value _ _ _ mapped
 cases unit
 exact native
#print axioms source
end NNH_Stage1ZeroOk
