import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_stateBefore {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let t ← read l.transcript
 let v ← r1_wire.SemanticTranscript.impl.state i.digest t
 pure (.inr (put s .record25b {l with stateBefore:=some v}))
theorem source_stateBefore {H : Type} (s : NLU.State H) (atSite : s.machine.next=.stateBefore) :
 NLU.step s=NLU.execute s (head_stateBefore s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_stateBefore s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_stateBefore
end AspisR1.NLU_Heads
end
