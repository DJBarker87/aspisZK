import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_mark5 {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 VerifyPrefix.mark none 5#u8
 pure (.inr (setNext s .circleGuard))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_mark5 {H : Type} (s : State H) (atSite : s.next = .mark5) :
 step s = window_mark5 s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_mark5
#print step_mark5
end AspisR1.NLC_Finish
end
