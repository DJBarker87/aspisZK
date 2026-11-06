import NLQ_LogPrefix
set_option autoImplicit false
noncomputable section
namespace NLQ_SnapshotEvents
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLM_Snapshot
/-- Exact source chronology of ALL completed snapshot events, not just the
three returned owned values. Each bracket has dropped before the next starts. -/
theorem chronology (e : Entry) :
 (NLQ_SnapshotFold.G e (.ok ()) (.ok ()) (.ok ())).events=
 (NLM_Snapshot.G (ready e 0 []) 0 58295 58295 (.ok ())).events++
 ((NLM_Snapshot.G (ready e 1 [e.snapshot 0 58295 58295]) 1 1880 1880 (.ok ())).events++
 (NLM_Snapshot.G (ready e 2 [e.snapshot 0 58295 58295,e.snapshot 1 1880 1880]) 2 1768 1768 (.ok ())).events) := by
 unfold NLQ_SnapshotFold.G
 simp only [Bind.bind,NJU_Log.bind,NLM_Snapshot.normal_result]
 rfl
#print axioms chronology
end NLQ_SnapshotEvents
