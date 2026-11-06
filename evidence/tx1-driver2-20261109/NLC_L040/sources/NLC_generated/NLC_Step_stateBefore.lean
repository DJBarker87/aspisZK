import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_stateBefore {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let t ← read l.transcript
 let v ← r1_wire.SemanticTranscript.impl.state i.digest t
 pure (.inr (put s .record25b {l with stateBefore:=some v}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_stateBefore {H : Type} (s : State H) (atSite : s.next = .stateBefore) :
 step s = window_stateBefore s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_stateBefore
#print step_stateBefore
end AspisR1.NLC_Finish
end
