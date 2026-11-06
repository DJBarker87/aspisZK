import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_multiply {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let terminal ← read l.terminal
 let product ← (IDa_Deployed.boundaries i.reservation).mul i.challenges.eta terminal
 pure (.inr (put s .addMask {l with product:=some product}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_multiply {H : Type} (s : State H) (atSite : s.next = .multiply) :
 step s = window_multiply s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_multiply
#print step_multiply
end AspisR1.NLC_Finish
end
