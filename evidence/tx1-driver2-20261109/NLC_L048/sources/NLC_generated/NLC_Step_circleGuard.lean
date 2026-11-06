import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_circleGuard {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let z0 ← read l.z0
 let z1 ← read l.z1
 let reject ← FinishModel.pointEq z0 z1
 if reject then pure (.inl (.Err r1_wire.Error.EqualCirclePoints))
 else pure (.inr (setNext s .payload2))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_circleGuard {H : Type} (s : State H) (atSite : s.next = .circleGuard) :
 step s = window_circleGuard s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_circleGuard
#print step_circleGuard
end AspisR1.NLC_Finish
end
