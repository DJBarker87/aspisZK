import NLQ_Stage1Result
import NLQ_SnapshotReplay
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1Fold
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
/-- Complete post-admission stage1 model: all three snapshots, owned child,
mutable acquire/deref/copy/Drop, then owned cleanup. Every abort keeps its
actual SDK/event priorEvents, computed from the SAME event chain. -/
def G (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (alloc0 alloc1 alloc2 : Result Unit) : Run :=
 let snapshots := NLQ_SnapshotFold.G e alloc0 alloc1 alloc2
 let priorEvents := snapshots.events.map Event.snapshot
 match snapshots.result with
 | .fail err => ⟨.fail err,
   ⟨NLQ_SnapshotReplay.replay (NLM_Snapshot.ready e 0 []) snapshots.events,none⟩,priorEvents⟩
 | .div => ⟨.div,
   ⟨NLQ_SnapshotReplay.replay (NLM_Snapshot.ready e 0 []) snapshots.events,none⟩,priorEvents⟩
 | .ok (_,post) =>
   let tail := continuation ops p d ⟨post,none⟩
   {tail with events:=priorEvents++tail.events}
/-- The three completed allocation branches lead to the exact suffix whose
copy-domain law was derived internally. No child success is a hypothesis. -/
theorem result (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) :
 (G e ops p d (.ok ()) (.ok ()) (.ok ())).result=
 (do let child ← AdapterRw.r1_pool_adapter.owned.stage1_owned ops p e.first d
     match child with
     | .Ok _ => ok (.Ok ())
     | .Err error => ok (.Err error)) := by
 simp only [G,NLQ_SnapshotFold.returned]
 exact NLQ_Stage1Result.result e ops p d
#print G
#print result
#print axioms result
end NLQ_Stage1Fold
