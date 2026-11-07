import NLU_State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Slots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
def LocalFrame {H : Type} (s : NLC_Finish.State H) (l : Locals H) : Prop :=
 (s.next≠.claims→l.claims=s.locals.claims) ∧ (s.next≠.rounds→l.alpha=s.locals.alpha)
def PostFrame {H : Type} (s : NLC_Finish.State H) : NLC_Finish.Post H → Prop
 | .inl _=>True
 | .inr after=>LocalFrame s after.locals
theorem put {H : Type} (s : NLC_Finish.State H) (e : NLC_Finish.Event) (l : Locals H)
 (same : LocalFrame s l) : PostFrame s (.inr (NLC_Finish.put s e l)) := same
theorem next {H : Type} (s : NLC_Finish.State H) (e : NLC_Finish.Event) :
 PostFrame s (.inr (setNext s e)) := ⟨fun _=>rfl,fun _=>rfl⟩
theorem returned {A H : Type} (s : NLC_Finish.State H) (e : NLC_Finish.Event)
 (r : core.result.Result A r1_wire.Error) (store : A → Locals H)
 (same : ∀ v,LocalFrame s (store v)) : PostFrame s (NLC_Finish.returned s e r store) := by
 cases r with
 | Ok value=>exact same value
 | Err err=>trivial
#print axioms put
#print axioms next
#print axioms returned
end AspisR1.NLU_Slots
end
