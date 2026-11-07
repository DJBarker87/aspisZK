import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_circleGuard {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let z0 ← read l.z0
 let z1 ← read l.z1
 let reject ← FinishModel.pointEq z0 z1
 if reject then pure (.inl (.Err r1_wire.Error.EqualCirclePoints))
 else pure (.inr (setNext s .payload2))
theorem source_circleGuard {H : Type} (s : NLU.State H) (atSite : s.machine.next=.circleGuard) :
 NLU.step s=NLU.execute s (head_circleGuard s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_circleGuard s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_circleGuard
end AspisR1.NLU_Heads
end
