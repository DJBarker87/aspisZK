import LIB_Carriers
import LIB_Mark
import NND_AccountLaws
import NND_ZeroCarrier
import NND_RegistryPredicates
import NMS_R2GetterLink
set_option autoImplicit false
noncomputable section
namespace LIB_Transcribed
open Aeneas Aeneas.Std AdapterRw
/-- Full getter law, including nonempty BorshIoError clone allocation. -/
theorem data (a : r1_pool_adapter.owned.OwnedAccount) :
    NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply LIB_Carriers.bytes)
      (NMS_R2N_GetterMeaning.meaning a)
      (NMS_R2N_RSLPoolCarriers.account a).data := NMS_R2GetterLink.full a
/-- Readonly laws are value-only: neither branch allocates or writes. -/
theorem readonlyBuffer (a : r1_pool_adapter.owned.OwnedAccount) :
    NND_Carrier.outer (NND_Carrier.reply id)
      (r1_pool_adapter.owned.require_readonly_buffer a) =
    .ok (RSL.readonlyBuffer (NND_Carrier.account a)) := NND_Carrier.readonly_buffer a
theorem readonlyAccount (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
    (p : solana_pubkey.Pubkey) :
    NND_Carrier.outer (NND_Carrier.reply id)
      (r1_pool_adapter.owned.require_readonly_account (NGL_ReadonlyModel.install ops) a p) =
    .ok (RSL.readonlyAccount (NND_Carrier.account a) (NND_Carrier.key p)) :=
  NND_Carrier.readonly ops a p
/-- Exact bounded CLOSED zero reference (the caller supplies the 1768-byte
checkpoint extent, which is below this CLOSED child's 4096 bound). -/
theorem zero (b : Slice U8) (bound : b.val.length ≤ 4096) :
    NND_Carrier.outer (NND_Carrier.reply id)
      (do let x ← NFQ_ScanReference.zero_ref b; pure (NFQ_ZeroSource.result x)) =
    .ok (RSL.requireZero (NND_Carrier.bytes b)) := NND_Carrier.closed_zero_reference b bound
#print axioms data
#print axioms readonlyBuffer
#print axioms readonlyAccount
#print axioms zero
end LIB_Transcribed
