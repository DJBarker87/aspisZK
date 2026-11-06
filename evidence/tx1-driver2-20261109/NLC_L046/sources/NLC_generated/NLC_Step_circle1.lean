import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_circle1 {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let t ← read l.transcript
 let rec ← read l.record26
 let (r,t1) ← S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest t rec
 pure (returned s .mark5 r (fun v => {l with z1:=some v, transcript:=some t1}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_circle1 {H : Type} (s : State H) (atSite : s.next = .circle1) :
 step s = window_circle1 s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_circle1
#print step_circle1
end AspisR1.NLC_Finish
end
