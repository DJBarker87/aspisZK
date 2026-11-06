import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_terminal {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let c ← read l.claims
 let a ← read l.alpha
 let r ← (IDa_Deployed.boundaries i.reservation).terminal i.publicValue c a i.challenges
 pure (.inr (put s .mapPublic {l with terminalReply:=some r}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_terminal {H : Type} (s : State H) (atSite : s.next = .terminal) :
 step s = window_terminal s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_terminal
#print step_terminal
end AspisR1.NLC_Finish
end
