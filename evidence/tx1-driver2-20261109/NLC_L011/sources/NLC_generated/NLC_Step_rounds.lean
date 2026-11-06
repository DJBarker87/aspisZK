import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_rounds {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let r ← S1SemanticCode.rounds NJM_RoundJoin.R i.digest i.prefix1 i.transcript
 pure (returned s .mark2 r (fun v => {l with running:=some v.1, alpha:=some v.2.1, transcript:=some v.2.2}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_rounds {H : Type} (s : State H) (atSite : s.next = .rounds) :
 step s = window_rounds s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_rounds
#print step_rounds
end AspisR1.NLC_Finish
end
