import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_rootCopy {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let payload ← read l.payload
 let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload
 let root ← (IDa_Deployed.boundaries i.reservation).unwrapRoot r
 pure (.inr (put s .verified {l with root:=some root}))
theorem source_rootCopy {H : Type} (s : NLU.State H) (atSite : s.machine.next=.rootCopy) :
 NLU.step s=NLU.execute s (head_rootCopy s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_rootCopy s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_rootCopy
end AspisR1.NLU_Heads
end
