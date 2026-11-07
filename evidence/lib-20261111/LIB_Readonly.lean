import LIB_Transcribed
import NGL_ReadonlyModel
import NND_CarrierInjective
set_option autoImplicit false
noncomputable section
namespace LIB_Readonly
open Aeneas Aeneas.Std Result AdapterRw
abbrev account := NMS_R2N_RSLPoolCarriers.account
abbrev key := NMS_R2N_RSLScalars.b32
theorem buffer (a : r1_pool_adapter.owned.OwnedAccount) :
  r1_pool_adapter.owned.require_readonly_buffer a =
  Result.ok (match RSL.readonlyBuffer (account a) with
    | .ok () => core.result.Result.Ok ()
    | .error _ => core.result.Result.Err .InvalidAccountData) := by
  unfold r1_pool_adapter.owned.require_readonly_buffer r1_pool_adapter.readonly_buffer_meta_ok
  cases hs : a.is_signer <;> cases hw : a.is_writable <;> cases he : a.executable <;>
    simp [RSL.readonlyBuffer,account,NMS_R2N_RSLPoolCarriers.account,hs,hw,he]
theorem owned (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount) (p : solana_pubkey.Pubkey) :
  r1_pool_adapter.owned.require_readonly_account (NGL_ReadonlyModel.install ops) a p =
  Result.ok (match RSL.readonlyAccount (account a) (key p) with
    | .ok () => core.result.Result.Ok ()
    | .error _ => core.result.Result.Err .InvalidAccountData) := by
  classical
  rw [NGL_ReadonlyModel.owned_result]
  have hk : decide (key a.owner = key p) = decide (a.owner = p) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact NND_Carrier.key_eq_iff a.owner p
  simp only [RSL.readonlyAccount,account,NMS_R2N_RSLPoolCarriers.account,decide_not]
  rw [hk]
  split <;> rfl
#print axioms buffer
#print axioms owned
end LIB_Readonly
