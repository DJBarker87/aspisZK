import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_multiply {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let terminal ← read l.terminal
 let product ← (IDa_Deployed.boundaries i.reservation).mul i.challenges.eta terminal
 pure (.inr (put s .addMask {l with product:=some product}))
theorem source_multiply {H : Type} (s : NLU.State H) (atSite : s.machine.next=.multiply) :
 NLU.step s=NLU.execute s (head_multiply s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_multiply s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_multiply
end AspisR1.NLU_Heads
end
