import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_lowArray {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let c ← read l.claims
 let low ← (IDa_Deployed.boundaries i.reservation).fromFn 16#usize (FinishModel.closureFn9 i.digest) c
 pure (.inr (put s .highArray {l with low:=some low}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_lowArray {H : Type} (s : State H) (atSite : s.next = .lowArray) :
 step s = window_lowArray s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_lowArray
#print step_lowArray
end AspisR1.NLC_Finish
end
