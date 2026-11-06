import NLM_SnapshotAcquire
set_option autoImplicit false
noncomputable section
namespace NLM_SnapshotFrames
open NLM_Snapshot NLF_SdkModel
/-- The SDK shared acquisition updates only its selected cell, preserving
all account descriptors and every other cell, including lamports cells. -/
theorem accounts (s : NLM_Snapshot.State) (a : Nat) :
 (acquired s a).accounts=s.sdk.accounts := rfl

theorem other_cell (s : NLM_Snapshot.State) (a i : Nat)
 (other : i≠(s.sdk.accounts a).data) : (acquired s a).cells i=s.sdk.cells i := by
 exact put_other s.sdk _ i _ other

theorem source_frame (s : NLM_Snapshot.State) (a : Nat) :
 (live s a).input=s.input ∧ (live s a).owned=s.owned ∧ (live s a).next=s.next+1 := ⟨rfl,rfl,rfl⟩
#print accounts
#print other_cell
#print source_frame
#print axioms accounts
#print axioms other_cell
#print axioms source_frame
end NLM_SnapshotFrames
