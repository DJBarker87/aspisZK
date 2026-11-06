import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_mask {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let low ← read l.low
 let high ← read l.high
 let blind ← read l.blind
 let alpha ← read l.alpha
 let mask ← (IDa_Deployed.boundaries i.reservation).mask low high blind alpha
 pure (.inr (put s .record25a {l with mask:=some mask}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_mask {H : Type} (s : State H) (atSite : s.next = .mask) :
 step s = window_mask s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_mask
#print step_mask
end AspisR1.NLC_Finish
end
