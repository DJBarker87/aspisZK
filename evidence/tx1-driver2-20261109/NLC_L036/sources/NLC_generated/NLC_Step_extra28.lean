import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_extra28 {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let extra ← read l.extra
 let v ← Array.index_usize extra 28#usize
 pure (.inr (put s .addExtra {l with extraCell:=some v}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_extra28 {H : Type} (s : State H) (atSite : s.next = .extra28) :
 step s = window_extra28 s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_extra28
#print step_extra28
end AspisR1.NLC_Finish
end
