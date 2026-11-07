import NLQ_Stage1Tail
import NLQ_Stage1Cases
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1ChildDiv
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
open AspisR1.S2W_D189Entry
/-- Full parent prefix/post for THIS child branch. Explicit input transport
avoids unfolding the entire emitted child while matching its arguments.
This is a local branch lemma; no child outcome is a row-root premise. -/
theorem source (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (branch : (NLD_Stage1Source.stage1Owned ops p e.first d).2=.div) :
 NLQ_Stage1Fold.G e ops p d (.ok ()) (.ok ()) (.ok ())=
 let s := NLQ_Stage1Ready.initial e
 ⟨.div,s,(NLQ_SnapshotFold.G e (.ok ()) (.ok ()) (.ok ())).events.map Event.snapshot++
  [.owned s s p e.first d .div (NLD_Stage1Source.stage1Owned ops p e.first d).1]⟩ := by
 let s := NLQ_Stage1Ready.initial e
 have child : (NLD_Stage1Source.stage1Owned ops p s.snapshots.input.first d).2=.div := by
  rw [show s.snapshots.input=e from rfl]
  exact branch
 have step := NLQ_Stage1Cases.child_diverge ops p d s child
 rw [NLQ_Stage1Tail.source]
 dsimp only
 rw [step]
 all_goals rfl
#print source
#print axioms source
end NLQ_Stage1ChildDiv
