import NDO_JHd_Authentication
import JHg_DataMaster
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_Authentication
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
/-- Same extracted continuation, with the corrected master read. -/
def afterRead (ops : Ops)
    (verifier pool : solana_pubkey.Pubkey) (lane : U8) (slot : U64)
    (ma ca la ra ea : r1_pool_adapter.owned.OwnedAccount) :
    Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts solana_program_error.ProgramError) := do
  let decoded ← ops.op48 JHg_DataMaster.value
  match decoded with
  | .Err e=>ok (.Err e)
  | .Ok master=>JHd_Authentication.afterMaster ops verifier pool lane slot ma ca la ra ea master
#print axioms afterRead
end AspisR1.JHi_Authentication
end
