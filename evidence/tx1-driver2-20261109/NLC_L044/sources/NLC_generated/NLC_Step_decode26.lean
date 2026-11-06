import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_decode26 {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let rec ← read l.record26
 let r ← NJM_RoundJoin.R.decode 29#usize rec 0#usize
 pure (returned s .record26b r (fun v => {l with beforeZ1:=some v}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_decode26 {H : Type} (s : State H) (atSite : s.next = .decode26) :
 step s = window_decode26 s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_decode26
#print step_decode26
end AspisR1.NLC_Finish
end
