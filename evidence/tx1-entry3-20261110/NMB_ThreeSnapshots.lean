import NMB_SnapshotReturn
import NLQ_SnapshotFold
set_option autoImplicit false
noncomputable section
namespace NMB_ThreeSnapshots
open Aeneas Aeneas.Std Result AspisR1 NMB_Snapshot
/-- Original per-occurrence snapshot array, before the owned child is called. -/
def first (x : NMB_Input.Input) : Slice Owned :=
 ⟨[x.snapshot 0 58295 58295,x.snapshot 1 1880 1880,x.snapshot 2 1768 1768],
  by simp; scalar_tac⟩
def G (x : NMB_Input.Input) (alloc0 alloc1 alloc2 : Result Unit) : Run (Slice Owned × State) := do
 let (proof,s1) ← NMB_Snapshot.G (ready x 0 []) 0 58295 58295 alloc0
 let (pub,s2) ← NMB_Snapshot.G s1 1 1880 1880 alloc1
 let (cp,s3) ← NMB_Snapshot.G s2 2 1768 1768 alloc2
 pure (NLQ_SnapshotFold.owned3 proof pub cp,s3)
def final (x : NMB_Input.Input) : State := ready x 3 (first x).val
/-- Each short-lived shared borrow restores its SAME SDK cell before the next
occurrence; only the token allocator and the owned prefix advance. -/
theorem result (x : NMB_Input.Input) :
 (G x (.ok ()) (.ok ()) (.ok ())).result = .ok (first x,final x) := by
 unfold G
 simp only [NJU_Log.erase_bind,NJU_Log.erase_pure]
 rw [NMB_SnapshotReturn.result]
 simp only [bind_tc_ok]
 change (do
  let (pub,s2) ← (NMB_Snapshot.G (ready x 1 [x.snapshot 0 58295 58295])
    1 1880 1880 (.ok ())).result
  let (cp,s3) ← (NMB_Snapshot.G s2 2 1768 1768 (.ok ())).result
  ok (NLQ_SnapshotFold.owned3 (x.snapshot 0 58295 58295) pub cp,s3)) = _
 rw [NMB_SnapshotReturn.result]
 simp only [bind_tc_ok]
 change (do
  let (cp,s3) ← (NMB_Snapshot.G
   (ready x 2 [x.snapshot 0 58295 58295,x.snapshot 1 1880 1880])
   2 1768 1768 (.ok ())).result
  ok (NLQ_SnapshotFold.owned3 (x.snapshot 0 58295 58295) (x.snapshot 1 1880 1880) cp,s3)) = _
 rw [NMB_SnapshotReturn.result]
 rfl
theorem entry_first (e : S2W_D189Entry.Entry) : first (NMB_Input.ofEntry e)=e.first := rfl
#print result
#print axioms result
#print axioms entry_first
end NMB_ThreeSnapshots
