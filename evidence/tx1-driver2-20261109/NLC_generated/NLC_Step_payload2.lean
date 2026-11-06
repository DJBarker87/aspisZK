import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_payload2 {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let r ← FinishModel.payload i.prefix1 2#u8
 pure (returned s .rootCopy r (fun v => {l with payload:=some v}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_payload2 {H : Type} (s : State H) (atSite : s.next = .payload2) :
 step s = window_payload2 s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_payload2
#print step_payload2
end AspisR1.NLC_Finish
end
