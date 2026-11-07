import NLQ_Stage1Tail
import NLQ_WritebackFrame
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1CopyPost
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
open AspisR1.S2W_D189Entry
/-- The actual successful owned-child occurrence is followed by the exact
copy/drop/cleanup run, after all three snapshot prefixes. Local branch only. -/
theorem source (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (saved : Bytes)
 (branch : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p e.first d=.ok (.Ok saved)) :
 NLQ_Stage1Fold.G e ops p d (.ok ()) (.ok ()) (.ok ())=
 let s := NLQ_Stage1Ready.initial e
 let out := copyResult s saved
 {out with events:=(NLQ_SnapshotFold.G e (.ok ()) (.ok ()) (.ok ())).events.map Event.snapshot++
  (.owned s s p e.first d (.ok (.Ok saved)) (NLD_Stage1Source.stage1Owned ops p e.first d).1)::out.events} := by
 have child : (NLD_Stage1Source.stage1Owned ops p e.first d).2=.ok (.Ok saved) :=
  (NLD_Stage1Source.erasure ops p e.first d).trans branch
 have site : (NLD_Stage1Source.stage1Owned ops p
   (NLQ_Stage1Ready.initial e).snapshots.input.first d).2=.ok (.Ok saved) := by
  rw [show (NLQ_Stage1Ready.initial e).snapshots.input=e from rfl]
  exact child
 rw [NLQ_Stage1Tail.source]
 dsimp only
 unfold continuation
 rw [site]
 all_goals rfl
#print source
#print axioms source
end NLQ_Stage1CopyPost
