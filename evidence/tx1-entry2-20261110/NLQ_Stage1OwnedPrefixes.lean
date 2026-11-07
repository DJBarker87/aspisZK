import NLQ_Stage1Tail
import NLQ_Stage1Cases
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1OwnedPrefixes
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
open AspisR1.S2W_D189Entry
/-- A reached child abort keeps the completed snapshot prefix and has no
copy or cleanup suffix. The branch is at THIS child expression, not a root. -/
theorem fail (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (err : Error)
 (branch : (NLD_Stage1Source.stage1Owned ops p e.first d).2=.fail err) :
 NLQ_Stage1Fold.G e ops p d (.ok ()) (.ok ()) (.ok ())=
 let s := NLQ_Stage1Ready.initial e
 ⟨.fail err,s,(NLQ_SnapshotFold.G e (.ok ()) (.ok ()) (.ok ())).events.map Event.snapshot++
  [.owned s s p e.first d (.fail err) (NLD_Stage1Source.stage1Owned ops p e.first d).1]⟩ := by
 rw [NLQ_Stage1Tail.source]
 dsimp only
 rw [NLQ_Stage1Cases.child_abort ops p d _ err branch]
 all_goals rfl
theorem div (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (branch : (NLD_Stage1Source.stage1Owned ops p e.first d).2=.div) :
 NLQ_Stage1Fold.G e ops p d (.ok ()) (.ok ()) (.ok ())=
 let s := NLQ_Stage1Ready.initial e
 ⟨.div,s,(NLQ_SnapshotFold.G e (.ok ()) (.ok ()) (.ok ())).events.map Event.snapshot++
  [.owned s s p e.first d .div (NLD_Stage1Source.stage1Owned ops p e.first d).1]⟩ := by
 rw [NLQ_Stage1Tail.source]
 dsimp only
 rw [NLQ_Stage1Cases.child_diverge ops p d _ branch]
 all_goals rfl
/-- Returned Err cleans owned temporaries after the error event, preserving
the complete SDK state. It is distinct from an outer fail/div prefix. -/
theorem error (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (err : PE)
 (branch : (NLD_Stage1Source.stage1Owned ops p e.first d).2=.ok (.Err err)) :
 NLQ_Stage1Fold.G e ops p d (.ok ()) (.ok ()) (.ok ())=
 let s := NLQ_Stage1Ready.initial e
 let post := {s with snapshots:={s.snapshots with owned:=[]}}
 ⟨.ok (.Err err),post,(NLQ_SnapshotFold.G e (.ok ()) (.ok ()) (.ok ())).events.map Event.snapshot++
  [.owned s s p e.first d (.ok (.Err err)) (NLD_Stage1Source.stage1Owned ops p e.first d).1,.cleanup s post]⟩ := by
 rw [NLQ_Stage1Tail.source]
 dsimp only
 rw [NLQ_Stage1Cases.child_error ops p d _ err branch]
 all_goals rfl
#print fail
#print div
#print error
#print axioms fail
#print axioms div
#print axioms error
end NLQ_Stage1OwnedPrefixes
