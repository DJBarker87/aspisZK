import NLQ_Stage1Abort
import NLQ_ReplayNormal
import NLQ_SnapshotEvents
import NLQ_SnapshotThirdPrefix
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1ThirdAbort
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
open AspisR1.S2W_D189Entry NLM_Snapshot
/-- Exact full parent post and attempted prefix at allocation 2. Prior
snapshots are completed at SAME arguments; the entered token remains LIVE.
This is a local branch lemma, not a root allocation-success premise. -/
theorem source (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (err : Error)
 (extent : (S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles 2).1)).length=1768) :
 NLQ_Stage1Fold.G e ops p d (.ok ()) (.ok ()) (.fail err) =
 let s := ready e 2 [e.snapshot 0 58295 58295,e.snapshot 1 1880 1880]
 ⟨(.fail err),⟨{s with sdk:=acquired s 2,next:=s.next+1},none⟩,
  ((NLM_Snapshot.G (ready e 0 []) 0 58295 58295 (.ok ())).events ++
  ((NLM_Snapshot.G (ready e 1 [e.snapshot 0 58295 58295]) 1 1880 1880 (.ok ())).events ++
  allocationPrefix s 2 (.fail err))).map Event.snapshot⟩ := by
 unfold NLQ_Stage1Fold.G
 rw [NLQ_SnapshotThirdPrefix.abort e err extent]
 dsimp only
 rw [NLQ_SnapshotReplay.append]
 rw [NLQ_SnapshotReplay.append]
 rw [NLQ_ReplayNormal.normal,NLQ_SnapshotEvents.returned_ready]
 simp only [List.nil_append,List.cons_append,Nat.zero_add]
 rw [NLQ_ReplayNormal.normal,NLQ_SnapshotEvents.returned_ready]
 simp only [List.nil_append,List.cons_append,Nat.zero_add]
 rw [NLQ_ReplayAbort.allocation]
#print source
#print axioms source
end NLQ_Stage1ThirdAbort
