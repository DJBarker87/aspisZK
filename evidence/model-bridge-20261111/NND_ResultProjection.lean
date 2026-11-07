import NND_ReplyForth
import NND_AccountCarrier
set_option autoImplicit false
namespace NND_ResultProjection
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier

theorem outer_ok {A B : Type} (f : A → B) (r : Result A) (b : B)
 (h : outer f r = ok b) : ∃ a, r = ok a ∧ f a = b := by
 cases r with
 | fail e => cases h
 | div => cases h
 | ok a => exact ⟨a,rfl,Result.ok.inj h⟩

theorem program_ok {A : Type} (r : Result (core.result.Result A solana_program_error.ProgramError))
 (b : Except RSL.ProgramError A) (h : outer (reply id) r = ok b) :
 r = ok (unreply id b) := by
 obtain ⟨a,ha,hb⟩ := outer_ok (reply id) r b h
 rw [ha]
 congr 1
 have back := congrArg (unreply id) hb
 rw [reply_back id id (fun _ => rfl)] at back
 exact back

#print axioms outer_ok
#print axioms program_ok
end NND_ResultProjection
