import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_blind {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let c ← read l.claims
 let row ← Array.index_usize c 0#usize
 let blind ← Array.index_usize row 27#usize
 pure (.inr (put s .alpha {l with blind:=some blind}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_blind {H : Type} (s : State H) (atSite : s.next = .blind) :
 step s = window_blind s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_blind
#print step_blind
end AspisR1.NLC_Finish
end
