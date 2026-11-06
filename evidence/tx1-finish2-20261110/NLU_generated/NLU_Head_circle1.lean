import NLU_Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Heads
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code)
/-- Exact source occurrence, with SAME immutable inputs and local slots.
This is a source/G step, not a native producer or child-domain premise. -/
def head_circle1 {H : Type} (s : NLC_Finish.State H) : Code (NLC_Finish.Post H) := do
 let i:=s.input
 let l:=s.locals
 let t ← read l.transcript
 let rec ← read l.record26
 let (r,t1) ← S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest t rec
 pure (returned s .mark5 r (fun v => {l with z1:=some v, transcript:=some t1}))
theorem source_circle1 {H : Type} (s : NLU.State H) (atSite : s.machine.next=.circle1) :
 NLU.step s=NLU.execute s (head_circle1 s.machine) := by
 rw [NLU.execute_step]
 have same : NLC_Finish.step s.machine=head_circle1 s.machine := by
  simp only [NLC_Finish.step,atSite]
  rfl
 rw [same]
#print axioms source_circle1
end AspisR1.NLU_Heads
end
