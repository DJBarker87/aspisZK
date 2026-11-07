import NMX_KeyCarrier
import NMX_ObserveResult
import NMX_LeafInstall
set_option autoImplicit false
noncomputable section
namespace NMX_ReadonlyCarrier
open Aeneas Aeneas.Std Result AdapterRw NMX_Carrier NMX_ObserveResult
attribute [local instance] Classical.propDecidable
/-- CLOSED readonly owner installed at SAME account/owner under one common
leaf installation; then transported to the canonical full observation. -/
theorem readonly (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (expected : solana_pubkey.Pubkey) :
 observe (fun u : Unit => u)
  (r1_pool_adapter.owned.require_readonly_account (NMX_LeafInstall.install ops) a expected) =
 ⟨.ret (RSL.readonlyAccount (account a) (key expected)),[]⟩ := by
 have closed := NHJ_ReadonlyPacket.readonly (NMX_LeafInstall.install ops) a expected
 change observe (fun u : Unit => u)
  (r1_pool_adapter.owned.require_readonly_account
   (NGL_ReadonlyModel.install (NMX_LeafInstall.install ops)) a expected) = _
 rw [closed]
 simp only [RSL.readonlyAccount,account,decide_not,NMX_KeyCarrier.key_equal,
  NHJ_ReadonlyPacket.G,NHJ_ReadonlyPacket.reply,NHJ_ReadonlyPacket.accepted]
 cases h : decide (a.owner = expected) <;> cases a.is_signer <;>
  cases a.is_writable <;> cases a.executable <;>
  simp [h,observe,NMX_Carrier.reply,NMX_Carrier.error]

/-- The proof-buffer helper uses its CLOSED NFU/NFQ source owner. -/
theorem proof (a : r1_pool_adapter.owned.OwnedAccount) :
 observe (fun u : Unit => u) (r1_pool_adapter.owned.require_readonly_buffer a) =
 ⟨.ret (RSL.readonlyBuffer (account a)),[]⟩ := by
 rw [NFU_AdapterGetters.readonly]
 cases a.is_signer <;> cases a.is_writable <;> cases a.executable <;>
  rfl
#print axioms readonly
#print axioms proof
end NMX_ReadonlyCarrier
end
