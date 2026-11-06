import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_mark4 {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 VerifyPrefix.mark none 4#u8
 pure (.inr (setNext s .stateBefore))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_mark4 {H : Type} (s : State H) (atSite : s.next = .mark4) :
 step s = window_mark4 s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_mark4
#print step_mark4
end AspisR1.NLC_Finish
end
