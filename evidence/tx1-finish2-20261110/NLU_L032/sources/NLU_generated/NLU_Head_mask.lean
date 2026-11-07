import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_mask {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let low ← read l.low
 let high ← read l.high
 let blind ← read l.blind
 let alpha ← read l.alpha
 let mask ← (IDa_Deployed.boundaries i.reservation).mask low high blind alpha
 pure (.inr (put s .record25a {l with mask:=some mask}))
theorem source_mask {H : Type} (s : NLU.State H) (atSite : s.machine.next=.mask) :
 NLU.step s=NLU.execute s (head_mask s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_mask s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_mask
end AspisR1.NLU_Heads
end
