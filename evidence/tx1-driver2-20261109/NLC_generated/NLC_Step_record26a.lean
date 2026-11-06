import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_record26a {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let r ← r1_wire.Prefix.validated_record i.prefix1 26#u8
 pure (returned s .decode26 r (fun v => {l with record26:=some v}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_record26a {H : Type} (s : State H) (atSite : s.next = .record26a) :
 step s = window_record26a s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_record26a
#print step_record26a
end AspisR1.NLC_Finish
end
