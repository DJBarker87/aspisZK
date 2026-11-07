import NNH_Tx2CheckpointPort
import NNH_MResultProjection
import NNH_MReadonlyPredicate
set_option autoImplicit false
noncomputable section
namespace NNH_AuthGuardPorts
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem readonly (base : Ops) (env : RSL.Env) (a : r1_pool_adapter.owned.OwnedAccount)
 (owner : solana_pubkey.Pubkey) :
 outer (reply id) (r1_pool_adapter.owned.require_readonly_account (NNH_Tx2ModelSlots.install base env) a owner)=
 .ok (RSL.readonlyAccount (account a) (key owner)) := by
 rw [NGL_ReadonlyModel.owned_result,NNH_MReadonlyPredicate.value]
 cases bad : (!decide (a.owner=owner) || a.is_signer || a.is_writable || a.executable) <;> rfl

theorem buffer (a : r1_pool_adapter.owned.OwnedAccount) :
 outer (reply id) (r1_pool_adapter.owned.require_readonly_buffer a)=.ok (RSL.readonlyBuffer (account a)) := by
 unfold r1_pool_adapter.owned.require_readonly_buffer r1_pool_adapter.readonly_buffer_meta_ok
 unfold RSL.readonlyBuffer
 cases signer : a.is_signer <;> cases writable : a.is_writable <;> cases executable : a.executable <;>
  simp only [account,signer,writable,executable,Bool.or_false,Bool.or_true,Bool.false_or,Bool.true_or,
   Bool.false_eq_true,if_false,if_true,outer,reply,NND_Carrier.error]

theorem data (base : Ops) (env : RSL.Env) (a : r1_pool_adapter.owned.OwnedAccount) :
 outer (reply NND_Carrier.bytes)
 (r1_pool_adapter.owned.OwnedAccount.data (NNH_Tx2ModelSlots.install base env) a)=.ok (account a).bytes := by
 exact NNH_ModelCarrier.getter (NNH_Tx2ModelSlots.install base env) a
#print axioms readonly
#print axioms buffer
#print axioms data
end NNH_AuthGuardPorts
