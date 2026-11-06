import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_addMask {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let mask ← read l.mask
 let product ← read l.product
 let v ← (IDa_Deployed.boundaries i.reservation).add mask product
 pure (.inr (put s .extra28 {l with partialValue:=some v}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_addMask {H : Type} (s : State H) (atSite : s.next = .addMask) :
 step s = window_addMask s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_addMask
#print step_addMask
end AspisR1.NLC_Finish
end
