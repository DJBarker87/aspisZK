import NLQ_SnapshotFold
import NLM_SnapshotPrefix
set_option autoImplicit false
noncomputable section
namespace NLQ_SnapshotThirdPrefix
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLM_Snapshot
/-- Two completed source snapshots precede the third allocation abort.
The live checkpoint token is 2; the exclusive-copy suffix is absent. -/
theorem abort (e : Entry) (err : Aeneas.Std.Error)
 (extent : (S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles 2).1)).length=1768) :
 NLQ_SnapshotFold.G e (.ok ()) (.ok ()) (.fail err) =
 ⟨.fail err,
  (NLM_Snapshot.G (ready e 0 []) 0 58295 58295 (.ok ())).events ++
  ((NLM_Snapshot.G (ready e 1 [e.snapshot 0 58295 58295]) 1 1880 1880 (.ok ())).events ++
  allocationPrefix (ready e 2 [e.snapshot 0 58295 58295,e.snapshot 1 1880 1880]) 2 (.fail err))⟩ := by
 unfold NLQ_SnapshotFold.G
 change NJU_Log.bind (NLM_Snapshot.G (ready e 0 []) 0 58295 58295 (.ok ())) _ = _
 unfold NJU_Log.bind
 rw [NLM_Snapshot.normal_result]
 dsimp only
 change (let rest : NLM_Snapshot.Run (Slice NLM_Snapshot.Owned × NLM_Snapshot.State) := do
   let (cp,s3) ← NLM_Snapshot.G (ready e 2 [e.snapshot 0 58295 58295,e.snapshot 1 1880 1880]) 2 1768 1768 (.fail err)
   pure (NLQ_SnapshotFold.owned3 (e.snapshot 0 58295 58295) (e.snapshot 1 1880 1880) cp,s3)
  ({result:=rest.result,events:=(NLM_Snapshot.G (ready e 0 []) 0 58295 58295 (.ok ())).events++
   ((NLM_Snapshot.G (ready e 1 [e.snapshot 0 58295 58295]) 1 1880 1880 (.ok ())).events++rest.events)}) = _
 rw [NLM_Snapshot.allocation_abort e 2 2 1768 1768 [e.snapshot 0 58295 58295,e.snapshot 1 1880 1880] err (Or.inl extent)]
 rfl
#check @abort
#print axioms abort
end NLQ_SnapshotThirdPrefix
