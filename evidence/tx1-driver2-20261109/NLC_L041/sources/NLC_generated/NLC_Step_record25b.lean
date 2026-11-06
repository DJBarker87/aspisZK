import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_record25b {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let r ← r1_wire.Prefix.validated_record i.prefix1 25#u8
 pure (returned s .circle0 r (fun v => {l with record25:=some v}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_record25b {H : Type} (s : State H) (atSite : s.next = .record25b) :
 step s = window_record25b s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_record25b
#print step_record25b
end AspisR1.NLC_Finish
end
