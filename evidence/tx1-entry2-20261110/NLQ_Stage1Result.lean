import NLQ_Stage1Ready
import NLQ_CheckpointDomain
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1Result
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
/-- The copy's length and exclusive-admission clauses are discharged from
THIS computed child arm and the restored snapshot state. -/
theorem copied (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key)
 (d : Slice U8) (saved : Bytes)
 (branch : AdapterRw.r1_pool_adapter.owned.stage1_owned ops p e.first d=.ok (.Ok saved)) :
 (copyResult (NLQ_Stage1Ready.initial e) saved).result=.ok (.Ok ()) := by
 have h := NLQ_Stage1Copy.copy e (S2W_ReturnedCheckpoint.nativeBytes saved)
  (NLQ_CheckpointDomain.same_length e ops p d saved branch)
 change (NLQ_CopyTrace.G (NLQ_Stage1Ready.initial e).snapshots.sdk 2
  (NLQ_Stage1Ready.initial e).snapshots.next (S2W_ReturnedCheckpoint.nativeBytes saved)).outcome=_ at h
 simp only [copyResult,h]
/-- Unconditional complete Result erasure of stage1's post-snapshot suffix.
The proof splits on the ACTUAL child expression internally, retaining inner
Err and outer fail/div. Ops remains an intermediate source installation. -/
theorem result (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) :
 (continuation ops p d (NLQ_Stage1Ready.initial e)).result=
 (do let child ← AdapterRw.r1_pool_adapter.owned.stage1_owned ops p e.first d
     match child with
     | .Ok _ => ok (.Ok ())
     | .Err error => ok (.Err error)) := by
 have source := NLD_Stage1Source.erasure ops p e.first d
 cases h : (NLD_Stage1Source.stage1Owned ops p e.first d).2 with
 | fail error =>
   rw [←source,h]
   simp only [continuation,NLQ_Stage1Ready.initial,NLQ_SnapshotFold.final,NLM_Snapshot.ready,h,bind_tc_fail]
 | div =>
   rw [←source,h]
   simp only [continuation,NLQ_Stage1Ready.initial,NLQ_SnapshotFold.final,NLM_Snapshot.ready,h,bind_tc_div]
 | ok reply =>
   cases reply with
   | Err error =>
     rw [←source,h]
     simp only [continuation,NLQ_Stage1Ready.initial,NLQ_SnapshotFold.final,NLM_Snapshot.ready,h,bind_tc_ok]
   | Ok saved =>
     have branch := source.symm.trans h
     rw [←source,h]
     simp only [continuation,NLQ_Stage1Ready.initial,NLQ_SnapshotFold.final,NLM_Snapshot.ready,h,bind_tc_ok]
     exact copied e ops p d saved branch
#check @result
#print axioms copied
#print axioms result
end NLQ_Stage1Result
