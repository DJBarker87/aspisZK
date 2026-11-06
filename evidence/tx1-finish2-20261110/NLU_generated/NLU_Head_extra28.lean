import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_extra28 {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let extra ← read l.extra
 let v ← Array.index_usize extra 28#usize
 pure (.inr (put s .addExtra {l with extraCell:=some v}))
theorem source_extra28 {H : Type} (s : NLU.State H) (atSite : s.machine.next=.extra28) :
 NLU.step s=NLU.execute s (head_extra28 s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_extra28 s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_extra28
end AspisR1.NLU_Heads
end
