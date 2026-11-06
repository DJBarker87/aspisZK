import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_claims {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let r ← (IDa_Deployed.boundaries i.reservation).claims i.prefix1
 pure (returned s .original r (fun v => {l with claims:=some v}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_claims {H : Type} (s : State H) (atSite : s.next = .claims) :
 step s = window_claims s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_claims
#print step_claims
end AspisR1.NLC_Finish
end
