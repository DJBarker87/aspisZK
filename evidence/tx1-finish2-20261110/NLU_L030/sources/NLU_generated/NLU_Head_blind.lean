import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_blind {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let c ← read l.claims
 let row ← Array.index_usize c 0#usize
 let blind ← Array.index_usize row 27#usize
 pure (.inr (put s .alpha {l with blind:=some blind}))
theorem source_blind {H : Type} (s : NLU.State H) (atSite : s.machine.next=.blind) :
 NLU.step s=NLU.execute s (head_blind s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_blind s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_blind
end AspisR1.NLU_Heads
end
