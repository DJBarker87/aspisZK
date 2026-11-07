import NLU_Linear
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Eliminate the actual resource step, never invert an independently chosen
native log. Both the next machine and owner come from that one head. -/
theorem next_characterization {H : Type} (s after : NLU.State H)
 (head : (step s).reply=.ok (.inr after)) :
 (PreparedHashCode.run (NLC_Finish.step s.machine)).2=.ok (.inr after.machine) ∧
 after.owner=carryOwner s := by
 unfold step at head
 cases h : PreparedHashCode.run (NLC_Finish.step s.machine) with
 | mk log reply =>
   rw [h] at head
   cases reply with
   | fail err => cases head
   | div => cases head
   | ok post =>
     cases post with
     | inr machine =>
       change (ok (Sum.inr (⟨machine,carryOwner s⟩ : NLU.State H) : Post H) : Result (Post H))=ok (Sum.inr after) at head
       have same:=Sum.inr.inj (Result.ok.inj head)
       cases same
       exact ⟨rfl,rfl⟩
     | inl out =>
       cases out with
       | Ok value => cases head
       | Err err =>
         simp only [carry] at head
         split at head <;> cases head
/-- The own input and its reservation survive every real continuation step. -/
theorem next_input {H : Type} (s after : NLU.State H)
 (head : (step s).reply=.ok (.inr after)) : after.machine.input=s.machine.input :=
 NLC_Finish.source_input_frame s.machine after.machine (next_characterization s after head).1
/-- The linear continuation invariant is derived, not a caller clause. -/
theorem next_linear {H : Type} (s after : NLU.State H) (before : Linear s)
 (head : (step s).reply=.ok (.inr after)) : Linear after := by
 have pair:=next_characterization s after head
 have invariant:=continuation_linear s after.machine before pair.1
 cases after with
 | mk machine owner =>
   have same : owner=carryOwner s := pair.2
   rw [same]
   exact invariant
#print axioms next_characterization
#print axioms next_input
#print axioms next_linear
end AspisR1.NLU
end
