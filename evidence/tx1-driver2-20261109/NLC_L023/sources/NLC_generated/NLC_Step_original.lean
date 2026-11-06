import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_original {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
re (.inr (setNext s .terminal))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_original {H : Type} (s : State H) (atSite : s.next = .original) :
 step s = window_original s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_original
#print step_original
end AspisR1.NLC_Finish
end
