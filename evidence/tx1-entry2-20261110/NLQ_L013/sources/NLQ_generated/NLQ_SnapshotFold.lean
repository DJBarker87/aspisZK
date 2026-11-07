import NLM_SnapshotReturn
import NLM_SnapshotPrefix
import NLQ_Route
set_option autoImplicit false
noncomputable section
namespace NLQ_SnapshotFold
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
open NLM_Snapshot
/-- Three source occurrences in stage1, on ONE state chain. Allocation
outcomes are parameters of this intermediate fold, not row-root hypotheses. -/
def G (e : Entry) (alloc0 alloc1 alloc2 : Result Unit) : Run (Slice NLM_Snapshot.Owned × State) := do
 let (proof,s1) ← NLM_Snapshot.G (ready e 0 []) 0 58295 58295 alloc0
 let (pub,s2) ← NLM_Snapshot.G s1 1 1880 1880 alloc1
 let (cp,s3) ← NLM_Snapshot.G s2 2 1768 1768 alloc2
 pure (⟨[proof,pub,cp],by simp; scalar_tac⟩,s3)
def final (e : Entry) : State := ready e 3
 [e.snapshot 0 58295 58295,e.snapshot 1 1880 1880,e.snapshot 2 1768 1768]
/-- The exact owned array and token state; every temporary guard is dropped
before the next acquire. Malformed extents remain deferred owned errors. -/
theorem returned (e : Entry) :
 (G e (.ok ()) (.ok ()) (.ok ())).result = .ok (e.first,final e) := by
 unfold G
 simp only [NJU_Log.erase_bind,NJU_Log.erase_pure]
 rw [NLM_Snapshot.normal_result]
 simp only [bind_tc_ok]
 change (do
  let (pub,s2) ← (NLM_Snapshot.G (ready e 1 [e.snapshot 0 58295 58295]) 1 1880 1880 (.ok ())).result
  let (cp,s3) ← (NLM_Snapshot.G s2 2 1768 1768 (.ok ())).result
  ok (⟨[e.snapshot 0 58295 58295,pub,cp],by simp; scalar_tac⟩,s3)) = _
 rw [NLM_Snapshot.normal_result]
 simp only [bind_tc_ok]
 change (do
  let (cp,s3) ← (NLM_Snapshot.G (ready e 2 [e.snapshot 0 58295 58295,e.snapshot 1 1880 1880]) 2 1768 1768 (.ok ())).result
  ok (⟨[e.snapshot 0 58295 58295,e.snapshot 1 1880 1880,cp],by simp; scalar_tac⟩,s3)) = _
 rw [NLM_Snapshot.normal_result]
 rfl
#print returned
#print axioms returned
end NLQ_SnapshotFold
