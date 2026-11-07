import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_mapPublic {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let r ← read l.terminalReply
 let r1 ← core.result.Result.map_err (FinishModel.closureFn11 i.digest) r ()
 pure (returned s .mark3 r1 (fun v => {l with terminal:=some v}))
theorem source_mapPublic {H : Type} (s : NLU.State H) (atSite : s.machine.next=.mapPublic) :
 NLU.step s=NLU.execute s (head_mapPublic s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_mapPublic s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_mapPublic
end AspisR1.NLU_Heads
end
