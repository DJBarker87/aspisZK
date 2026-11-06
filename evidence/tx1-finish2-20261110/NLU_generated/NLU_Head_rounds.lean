import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_rounds {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
   let r ← S1SemanticCode.rounds NJM_RoundJoin.R i.digest i.prefix1 i.transcript
   pure (returned s .mark2 r (fun v => {l with running:=some v.1, alpha:=some v.2.1, transcript:=some v.2.2}))
theorem source_rounds {H : Type} (s : NLU.State H) (atSite : s.machine.next=.rounds) :
 NLU.step s=NLU.execute s (head_rounds s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_rounds s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_rounds
end AspisR1.NLU_Heads
end
