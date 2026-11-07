import NMT_345ReadonlyProof
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Separate second occurrence: original public account, SAME parent state. -/
def readonlyPublicStep {W : Type} (s : Selected W) (next : Selected W → Result Ret) : Result Ret :=
 tryStep (readonlyCall s.publicAccount) (fun _ => next s)
theorem readonlyPublic_closed {W : Type} (s : Selected W) (next : Selected W → Result Ret) :
 readonlyPublicStep s next =
 if s.publicAccount.is_signer || s.publicAccount.is_writable || s.publicAccount.executable
 then .ok (.Err .InvalidAccountData) else next s := by
 unfold readonlyPublicStep
 rw [readonly_closed]
 split <;> rfl
#print axioms readonlyPublic_closed
end NMT_345
