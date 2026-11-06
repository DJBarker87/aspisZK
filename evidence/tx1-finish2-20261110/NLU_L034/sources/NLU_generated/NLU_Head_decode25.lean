import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_decode25 {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let record ← read l.record25
 let r ← NJM_RoundJoin.R.decode 29#usize record 87#usize
 pure (returned s .multiply r (fun v => {l with extra:=some v}))
theorem source_decode25 {H : Type} (s : NLU.State H) (atSite : s.machine.next=.decode25) :
 NLU.step s=NLU.execute s (head_decode25 s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_decode25 s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_decode25
end AspisR1.NLU_Heads
end
