import NNH_MAccountCarrier
import NND_CarrierInjective
import NGL_ReadonlyModel
import NGL_CloneDomain
set_option autoImplicit false
noncomputable section
namespace NNH_ModelCarrier
open NND_Carrier NNH_ModelCarrier
open Aeneas Aeneas.Std Result AdapterRw

theorem length (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount) :
 outer (reply (fun n : Usize => n.val))
 (r1_pool_adapter.owned.OwnedAccount.data_len (NGL_CloneDomain.install ops) a) =
 ok ((account a).length) := by
 rw [NGL_CloneDomain.length_result]
 cases h : a.length <;> simp [account,h,outer,reply]

theorem readonly (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount) (p : solana_pubkey.Pubkey) :
 outer (reply id)
 (r1_pool_adapter.owned.require_readonly_account (NGL_ReadonlyModel.install ops) a p) =
 ok (RSL.readonlyAccount (account a) (key p)) := by
 classical
 rw [NGL_ReadonlyModel.owned_result]
 have hk : decide (key a.owner = key p) = decide (a.owner = p) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact key_eq_iff a.owner p
 simp only [RSL.readonlyAccount,account,decide_not]
 rw [hk]
 split <;> rfl

theorem readonly_buffer (a : r1_pool_adapter.owned.OwnedAccount) :
 outer (reply id) (r1_pool_adapter.owned.require_readonly_buffer a) =
 ok (RSL.readonlyBuffer (account a)) := by
 unfold r1_pool_adapter.owned.require_readonly_buffer r1_pool_adapter.readonly_buffer_meta_ok
 cases hs : a.is_signer <;> cases hw : a.is_writable <;> cases he : a.executable <;>
 simp [RSL.readonlyBuffer,account,hs,hw,he,outer,reply,error]

#print axioms length
#print axioms readonly
#print axioms readonly_buffer
end NNH_ModelCarrier
