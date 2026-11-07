import NMT_345Distinct
import NMT_345RSLCarriers
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result

def readonlyCall (a : Account) : Result (core.result.Result Unit PE) :=
 mapOuter (mapCore id fromPE)
  (AdapterRw.r1_pool_adapter.owned.require_readonly_buffer (toAccount a))
/-- CLOSED340, at the SAME first proof-account occurrence. No child domain. -/
theorem readonly_closed (a : Account) : readonlyCall a =
 .ok (if a.is_signer || a.is_writable || a.executable then .Err .InvalidAccountData else .Ok ()) := by
 unfold readonlyCall
 rw [NFU_AdapterGetters.readonly]
 simp only [toAccount]
 cases a.is_signer <;> cases a.is_writable <;> cases a.executable <;> rfl

theorem readonly_canonical (a : Account) :
 mapOuter (rustResult id) (readonlyCall a) = .ok (RSL.readonlyBuffer (account a)) := by
 rw [readonly_closed]
 unfold RSL.readonlyBuffer account
 cases a.is_signer <;> cases a.is_writable <;> cases a.executable <;> rfl

def readonlyProofStep {W : Type} (s : Selected W) (next : Selected W → Result Ret) : Result Ret :=
 tryStep (readonlyCall s.proofAccount) (fun _ => next s)
theorem readonlyProof_closed {W : Type} (s : Selected W) (next : Selected W → Result Ret) :
 readonlyProofStep s next =
 if s.proofAccount.is_signer || s.proofAccount.is_writable || s.proofAccount.executable
 then .ok (.Err .InvalidAccountData) else next s := by
 unfold readonlyProofStep
 rw [readonly_closed]
 split <;> rfl
#print axioms readonly_closed
#print axioms readonly_canonical
#print axioms readonlyProof_closed
end NMT_345
