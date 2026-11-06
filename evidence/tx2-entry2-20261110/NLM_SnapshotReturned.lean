import NLM_SnapshotSkip
set_option autoImplicit false
noncomputable section
namespace NLM_Snapshot
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- Entering the next cut derives the exact snapshot/state; no allocation
success premise is introduced. A rejected length skips allocation entirely. -/
theorem returned_normal (e : Entry) (t a lo hi : Nat) (owned : List Owned)
 (allocation : Result Unit) (value : NLM_Snapshot.Owned) (post : State)
 (entered : (G (ready e t owned) a lo hi allocation).result=.ok (value,post)) :
 G (ready e t owned) a lo hi allocation=G (ready e t owned) a lo hi (.ok ()) := by
 by_cases copy : (AspisR1.S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1)).length=lo ∨
                (AspisR1.S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1)).length=hi
 · cases allocation with
   | ok unit => cases unit; rfl
   | fail err => rw [allocation_abort e t a lo hi owned err copy] at entered; cases entered
   | div => rw [allocation_diverge e t a lo hi owned copy] at entered; cases entered
 · exact skip_allocation e t a lo hi owned allocation copy

theorem returned_state (e : Entry) (t a lo hi : Nat) (owned : List Owned)
 (allocation : Result Unit) (value : NLM_Snapshot.Owned) (post : State)
 (entered : (G (ready e t owned) a lo hi allocation).result=.ok (value,post)) :
 value=e.snapshot a lo hi ∧ post=returned (ready e t owned) a lo hi := by
 rw [returned_normal e t a lo hi owned allocation value post entered,normal_result] at entered
 cases entered
 exact ⟨rfl,rfl⟩
#print returned_normal
#print returned_state
#print axioms returned_normal
#print axioms returned_state
end NLM_Snapshot
