import NLU_State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Native child reservation action is part of claims129, not an extra
allocation at the caller. This avoids NLI's duplicate independent allocator. -/
def entered {H : Type} (s : NLU.State H) : List NLU.Event :=
 [.occurrence s.machine.next] ++
 (if s.machine.next = .claims then [.claims s.machine.input.reservation] else []) ++
 (if s.machine.next = .terminal ∨ s.machine.next = .lowArray ∨
     s.machine.next = .highArray ∨ s.machine.next = .blind then [.borrow] else [])
def carryOwner {H : Type} (s : NLU.State H) : Owner :=
 if s.machine.next = .claims then .live else s.owner
/-- Called only on returning source steps. No abort branch reaches release. -/
def carry {H : Type} (s : NLU.State H) (post : NLC_Finish.Post H) : List NLU.Event × Post H :=
 match post with
 | .inr after =>
   (if s.machine.next = .claims then [.acquire] else [], .inr ⟨after,carryOwner s⟩)
 | .inl out =>
   match out with
   | .Err err =>
     if s.owner = .live then ([.release], .inl (.Err err,.dropped))
     else ([], .inl (.Err err,s.owner))
   | .Ok value => ([.transfer], .inl (.Ok value,.transferred))
def step {H : Type} (s : NLU.State H) : StepObservation H :=
 let head := PreparedHashCode.run (NLC_Finish.step s.machine)
 let events := entered s ++ head.1.map NLU.Event.digest
 match head.2 with
 | .fail e => ⟨s.machine.input,events,.fail e⟩
 | .div => ⟨s.machine.input,events,.div⟩
 | .ok post =>
   let next := carry s post
   ⟨s.machine.input,events ++ next.1,.ok next.2⟩
/-- Projection only: resource bookkeeping never substitutes a source reply.
Native fidelity of the bookkeeping remains a separate reviewed-cut obligation. -/
theorem carry_projection {H : Type} (s : NLU.State H) (post : NLC_Finish.Post H) :
 erasePost (carry s post).2=post := by
 cases post with
 | inr after => rfl
 | inl out =>
   cases out with
   | Ok value => rfl
   | Err err => simp only [carry];split <;> rfl
#print axioms carry_projection
end AspisR1.NLU
end
