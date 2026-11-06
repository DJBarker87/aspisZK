import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_decode25 {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let record ← read l.record25
 let r ← NJM_RoundJoin.R.decode 29#usize record 87#usize
 pure (returned s .multiply r (fun v => {l with extra:=some v}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_decode25 {H : Type} (s : State H) (atSite : s.next = .decode25) :
 step s = window_decode25 s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_decode25
#print step_decode25
end AspisR1.NLC_Finish
end
