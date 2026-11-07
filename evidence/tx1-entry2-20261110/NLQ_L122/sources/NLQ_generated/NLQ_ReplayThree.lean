import NLQ_ReplayNormal
import NLQ_SnapshotEvents
set_option autoImplicit false
noncomputable section
namespace NLQ_ReplayThree
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLM_Snapshot
/-- The entire completed snapshot event list replays to the SAME returned
state, not a separately chosen endpoint or successful borrowed execution. -/
theorem complete (e : Entry) :
 NLQ_SnapshotReplay.replay (ready e 0 [])
  (NLQ_SnapshotFold.G e (.ok ()) (.ok ()) (.ok ())).events = NLQ_SnapshotFold.final e := by
 rw [NLQ_SnapshotEvents.chronology,NLQ_SnapshotReplay.append,NLQ_SnapshotReplay.append]
 rw [NLQ_ReplayNormal.normal]
 rw [NLQ_SnapshotEvents.returned_ready]
 simp only [List.nil_append,List.cons_append,Nat.zero_add]
 rw [NLQ_ReplayNormal.normal]
 rw [NLQ_SnapshotEvents.returned_ready]
 simp only [List.nil_append,List.cons_append,Nat.zero_add]
 rw [NLQ_ReplayNormal.normal]
 rfl
#print complete
#print axioms complete
end NLQ_ReplayThree
