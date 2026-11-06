import NLQ_Stage1State
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1Cases
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
/-- The complete child result is COMPUTED; each clause is a local reduction
lemma, never a proposed root assumption. Native parent cuts are still OPEN. -/
theorem child_abort (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (s : State)
 (e : Error) (aborted : (AspisR1.NLD_Stage1Source.stage1Owned ops p s.snapshots.input.first d).2=.fail e) :
 continuation ops p d s =
 ⟨.fail e,s,[.owned s s p s.snapshots.input.first d (.fail e)
   (AspisR1.NLD_Stage1Source.stage1Owned ops p s.snapshots.input.first d).1]⟩ := by
 simp only [continuation,aborted]
theorem child_diverge (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (s : State)
 (aborted : (AspisR1.NLD_Stage1Source.stage1Owned ops p s.snapshots.input.first d).2=.div) :
 continuation ops p d s =
 ⟨.div,s,[.owned s s p s.snapshots.input.first d .div
   (AspisR1.NLD_Stage1Source.stage1Owned ops p s.snapshots.input.first d).1]⟩ := by
 simp only [continuation,aborted]
theorem child_error (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (s : State)
 (e : PE) (rejected : (AspisR1.NLD_Stage1Source.stage1Owned ops p s.snapshots.input.first d).2=.ok (.Err e)) :
 let after := {s with snapshots:={s.snapshots with owned:=[]}}
 continuation ops p d s =
 ⟨.ok (.Err e),after,[.owned s s p s.snapshots.input.first d (.ok (.Err e))
   (AspisR1.NLD_Stage1Source.stage1Owned ops p s.snapshots.input.first d).1,.cleanup s after]⟩ := by
 simp only [continuation,rejected]
#print axioms child_abort
#print axioms child_diverge
#print axioms child_error
end NLQ_Stage1Cases
