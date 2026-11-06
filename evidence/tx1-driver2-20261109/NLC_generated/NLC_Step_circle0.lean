import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_circle0 {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let t ← read l.transcript
 let rec ← read l.record25
 let (r,t1) ← S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest t rec
 pure (returned s .record26a r (fun v => {l with z0:=some v, transcript:=some t1}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_circle0 {H : Type} (s : State H) (atSite : s.next = .circle0) :
 step s = window_circle0 s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_circle0
#print step_circle0
end AspisR1.NLC_Finish
end
