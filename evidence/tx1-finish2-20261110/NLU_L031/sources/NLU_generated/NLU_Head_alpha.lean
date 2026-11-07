import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_alpha {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 pure (.inr (setNext s .mask))
theorem source_alpha {H : Type} (s : NLU.State H) (atSite : s.machine.next=.alpha) :
 NLU.step s=NLU.execute s (head_alpha s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_alpha s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_alpha
end AspisR1.NLU_Heads
end
