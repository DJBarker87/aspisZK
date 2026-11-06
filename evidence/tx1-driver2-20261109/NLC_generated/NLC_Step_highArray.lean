import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_highArray {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let c ← read l.claims
 let high ← (IDa_Deployed.boundaries i.reservation).fromFn 10#usize (FinishModel.closureFn5 i.digest) c
 pure (.inr (put s .blind {l with high:=some high}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_highArray {H : Type} (s : State H) (atSite : s.next = .highArray) :
 step s = window_highArray s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_highArray
#print step_highArray
end AspisR1.NLC_Finish
end
