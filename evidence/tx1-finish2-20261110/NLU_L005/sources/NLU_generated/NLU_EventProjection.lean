import NLU_Fold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
def digestLog (events : List NLU.Event) : PreparedHashCode.Log :=
 events.filterMap (fun e => match e with | .digest e => some e | _ => none)
theorem digest_append (a b : List NLU.Event) : digestLog (a++b)=digestLog a++digestLog b := by
 exact List.filterMap_append
theorem entered_digest {H : Type} (s : NLU.State H) : digestLog (entered s)=[] := by
 unfold entered
 simp only [digest_append]
 split <;> split <;> rfl
theorem carry_digest {H : Type} (s : NLU.State H) (post : NLC_Finish.Post H) :
 digestLog (carry s post).1=[] := by
 cases post with
 | inr after => unfold carry;split <;> rfl
 | inl out => cases out with
   | Ok value => rfl
   | Err err => unfold carry;split <;> rfl
theorem map_digest (events : PreparedHashCode.Log) : digestLog (events.map NLU.Event.digest)=events := by
 induction events with
 | nil => rfl
 | cons e es ih => change e::digestLog (es.map NLU.Event.digest)=e::es;rw [ih]
#print axioms digest_append
#print axioms entered_digest
#print axioms carry_digest
#print axioms map_digest
end AspisR1.NLU
end
