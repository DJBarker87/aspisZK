import NNH_AuthGuardPorts
import NNH_MappedOk
set_option autoImplicit false
noncomputable section
namespace NNH_GetterOk
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier
/-- Preserve the actual getter's returned slice. No independent byte buffer
or successful native call is introduced as a premise. -/
theorem value (base : Ops) (env : RSL.Env) (a : r1_pool_adapter.owned.OwnedAccount)
 (data : RSL.Bytes) (success : (account a).bytes=.ok data) :
 ∃ b,r1_pool_adapter.owned.OwnedAccount.data (NNH_Tx2ModelSlots.install base env) a=.ok (.Ok b) ∧ bytes b=data := by
 have mapped := NNH_AuthGuardPorts.data base env a
 rw [success] at mapped
 exact NNH_MappedOk.value _ _ _ mapped
#print axioms value
end NNH_GetterOk
