import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run erase)
/-- Stronger than returning-run purity: the frame holds for every possible
reply at each Code node, including continuations not reached by this digest. -/
def AllLeaves {A : Type} (P : A → Prop) : Code A → Prop
 | .done a => P a
 | .step _ next => ∀ b, AllLeaves P (next b)
 | .digest _ _ _ next => ∀ b, AllLeaves P (next b)
theorem all_bind {A B : Type} (p : Code A) (k : A → Code B) (P : B → Prop)
 (tails : ∀ a, AllLeaves P (k a)) : AllLeaves P (PreparedHashCode.bind p k) := by
 induction p with
 | done a => exact tails a
 | step _ _ ih => exact fun b => ih b
 | digest _ _ _ _ ih => exact fun b => ih b

def FramePost {H : Type} (s : State H) : Post H → Prop
 | .inl _ => True
 | .inr after => InputFrame s after

theorem returned_frame {A H : Type} (s : State H) (e : Event)
 (r : core.result.Result A r1_wire.Error) (store : A → Locals H) :
 FramePost s (returned s e r store) := by
 cases r with
 | Ok a => rfl
 | Err err => trivial

theorem frame_put {H : Type} (s : State H) (e : Event) (l : Locals H) :
 FramePost s (.inr (put s e l)) := rfl

theorem frame_next {H : Type} (s : State H) (e : Event) :
 FramePost s (.inr (setNext s e)) := rfl
#print axioms all_bind
#print axioms returned_frame
#print axioms frame_put
#print axioms frame_next
end AspisR1.NLC_Finish
end
