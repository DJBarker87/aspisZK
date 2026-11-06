import NLQ_SnapshotPrefixes
set_option autoImplicit false
noncomputable section
namespace NLQ_SnapshotLaterPrefixes
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLM_Snapshot
/-- Retain the actual successful first snapshot's events, then the exact
second allocation abort. Its live token is1; there is no checkpoint snapshot. -/
theorem second_abort (e : Entry) (err : Aeneas.Std.Error) (a2 : Result Unit)
 (extent : (S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles 1).1)).length=1880) :
 NLQ_SnapshotFold.G e (.ok ()) (.fail err) a2 =
 ⟨.fail err,(NLM_Snapshot.G (ready e 0 []) 0 58295 58295 (.ok ())).events ++
  allocationPrefix (ready e 1 [e.snapshot 0 58295 58295]) 1 (.fail err)⟩ := by
 unfold NLQ_SnapshotFold.G
 change NJU_Log.bind (NLM_Snapshot.G (ready e 0 []) 0 58295 58295 (.ok ())) _ = _
 unfold NJU_Log.bind
 rw [NLM_Snapshot.normal_result]
 change (let rest : NLM_Snapshot.Run (Slice NLM_Snapshot.Owned × NLM_Snapshot.State) := do
   let (pub,s2) ← NLM_Snapshot.G (ready e 1 [e.snapshot 0 58295 58295]) 1 1880 1880 (.fail err)
   let (cp,s3) ← NLM_Snapshot.G s2 2 1768 1768 a2
   pure (NLQ_SnapshotFold.owned3 (e.snapshot 0 58295 58295) pub cp,s3)
  ({result:=rest.result,events:=(NLM_Snapshot.G (ready e 0 []) 0 58295 58295 (.ok ())).events++rest.events} : NLM_Snapshot.Run (Slice NLM_Snapshot.Owned × NLM_Snapshot.State))) = _
 rw [NLM_Snapshot.allocation_abort e 1 1 1880 1880 [e.snapshot 0 58295 58295] err (Or.inl extent)]
 rfl
#check @second_abort
#print axioms second_abort
end NLQ_SnapshotLaterPrefixes
