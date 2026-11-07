import NMX_R2_ObserveResult
import NMX_R2_KeyCarrier
import NMX_ClosedLeaves
set_option autoImplicit false
noncomputable section
namespace NMX_R2_ReadonlyNative
open Aeneas Aeneas.Std Result AdapterRw NMX_R2_Carrier
attribute [local instance] Classical.propDecidable
/-- All metadata arms of the actual frozen helper, with arbitrary stored
bytes/errors. The CLOSED readonly owner is used at the same arguments. -/
theorem account (base : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (expected : solana_pubkey.Pubkey) (env : RSL.Env) :
 RSL.RS.ofExcept (RSL.readonlyAccount (NMX_R2_Carrier.account a) (key expected)) env
  (NMX_R2_ObserveResult.observe id
   (r1_pool_adapter.owned.require_readonly_account (NGL_ReadonlyModel.install base) a expected)) := by
 rw [NGL_ReadonlyModel.owned_result]
 change RSL.RS.ofExcept
  (if decide (key a.owner ≠ key expected) || a.is_signer || a.is_writable || a.executable
   then .error .invalidAccountData else .ok ()) env _
 simp only [ne_eq,NMX_R2_KeyCarrier.key_equal,decide_not]
 cases h : (!(decide (a.owner=expected)) || a.is_signer || a.is_writable || a.executable) <;> rfl

theorem buffer (a : r1_pool_adapter.owned.OwnedAccount) (env : RSL.Env) :
 RSL.RS.ofExcept (RSL.readonlyBuffer (NMX_R2_Carrier.account a)) env
  (NMX_R2_ObserveResult.observe id (r1_pool_adapter.owned.require_readonly_buffer a)) := by
 unfold r1_pool_adapter.owned.require_readonly_buffer r1_pool_adapter.readonly_buffer_meta_ok
 change RSL.RS.ofExcept
  (if a.is_signer || a.is_writable || a.executable then .error .invalidAccountData else .ok ()) env _
 cases a.is_signer <;> cases a.is_writable <;> cases a.executable <;> rfl
#print axioms account
#print axioms buffer
end NMX_R2_ReadonlyNative
end
