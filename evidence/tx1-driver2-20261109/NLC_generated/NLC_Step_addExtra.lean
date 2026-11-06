import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_addExtra {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let x ← read l.partialValue
 let y ← read l.extraCell
 let masked ← (IDa_Deployed.boundaries i.reservation).add x y
 pure (.inr (put s .terminalGuard {l with masked:=some masked}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_addExtra {H : Type} (s : State H) (atSite : s.next = .addExtra) :
 step s = window_addExtra s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_addExtra
#print step_addExtra
end AspisR1.NLC_Finish
end
