import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_alpha {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 pure (.inr (setNext s .mask))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_alpha {H : Type} (s : State H) (atSite : s.next = .alpha) :
 step s = window_alpha s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_alpha
#print step_alpha
end AspisR1.NLC_Finish
end
