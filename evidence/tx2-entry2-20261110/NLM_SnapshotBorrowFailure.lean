import NLM_SnapshotState
set_option autoImplicit false
noncomputable section
namespace NLM_SnapshotBorrowFailure
open Aeneas Aeneas.Std NLM_Snapshot
/-- Exact source value on the actual SDK error arm; no allocator is called. -/
def value (s : NLM_Snapshot.State) (a lo hi : Nat) : NLM_Snapshot.Owned :=
 {(s.input.snapshot a lo hi) with length:=.Err .AccountBorrowFailed,bytes:=.Err .AccountBorrowFailed}

theorem failed (s : NLM_Snapshot.State) (a lo hi : Nat) (allocation : Result Unit)
 (err : NLF_SdkModel.ProgramError)
 (failure : NLF_SdkModel.try_borrow_data s.sdk a s.next=(s.sdk,.error err)) :
 G s a lo hi allocation=
 ⟨.ok (value s a lo hi,{s with next:=s.next+1,owned:=s.owned++[value s a lo hi]}),
 [.acquire s a s.next s.sdk (.ok (.error err)),.returned s a lo hi (.ok (value s a lo hi))]⟩ := by
 unfold G
 rw [failure]
 rfl
#print failed
#print axioms failed
end NLM_SnapshotBorrowFailure
