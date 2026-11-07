import NMX_KeyCarrier
import NMX_ObserveResult
import NMX_LeafInstall
set_option autoImplicit false
noncomputable section
namespace NMX_ReadonlyCarrier
open Aeneas Aeneas.Std Result AdapterRw NMX_Carrier NMX_ObserveResult
attribute [local instance] Classical.propDecidable

/-- Two fixed Bool arms; keep the actual account/decision expression folded. -/
theorem unit_reflection (bad : Bool) :
 observe (fun u : Unit => u)
  (ok (if !bad then core.result.Result.Ok () else .Err .InvalidAccountData)) =
 ⟨.ret (if bad then Except.error RSL.ProgramError.invalidAccountData else Except.ok ()),[]⟩ := by
 cases bad <;> rfl

theorem buffer (signer writable executable : Bool) :
 observe (fun u : Unit => u)
  (do let admitted ← NFQ_ScanReference.readonly_buffer_ref signer writable executable
      ok (if admitted then core.result.Result.Ok () else .Err .InvalidAccountData)) =
 ⟨.ret (if signer || writable || executable then
   Except.error RSL.ProgramError.invalidAccountData else Except.ok ()),[]⟩ := by
 cases signer <;> cases writable <;> cases executable <;> rfl
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
 exact unit_reflection (!(decide (a.owner = expected)) || a.is_signer || a.is_writable || a.executable)

/-- The proof-buffer helper uses its CLOSED NFU/NFQ source owner. -/
theorem proof (a : r1_pool_adapter.owned.OwnedAccount) :
 observe (fun u : Unit => u) (r1_pool_adapter.owned.require_readonly_buffer a) =
 ⟨.ret (RSL.readonlyBuffer (account a)),[]⟩ := by
 rw [NFU_AdapterGetters.readonly]
 exact buffer a.is_signer a.is_writable a.executable
#print axioms unit_reflection
#print axioms buffer
#print axioms readonly
#print axioms proof
end NMX_ReadonlyCarrier
end
