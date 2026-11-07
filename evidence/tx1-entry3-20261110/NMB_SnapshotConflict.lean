import NMB_Snapshot
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotConflict
open Aeneas Aeneas.Std Result AspisR1 NLF_RefCell NLF_SdkModel NMB_Snapshot
/-- General pre-state SDK conflict: exact deferred error and metadata, no
allocator call, no fabricated guard, no release. -/
theorem conflict (s : NMB_Snapshot.State) (a lo hi : Nat) (allocation : Result Unit)
 (bad : try_borrow_data s.sdk a s.next=(s.sdk,.error .accountBorrowFailed)) :
 let value := {(s.input.descriptors a) with
   length:=core.result.Result.Err AdapterRw.solana_program_error.ProgramError.AccountBorrowFailed,
   bytes:=core.result.Result.Err AdapterRw.solana_program_error.ProgramError.AccountBorrowFailed}
 G s a lo hi allocation =
 ⟨.ok (value,{s with next:=s.next+1,owned:=s.owned++[value]}),
 [.acquire s a s.next s.sdk (.ok (.error .accountBorrowFailed)),
  .returned s a lo hi (.ok value)]⟩ := by
 dsimp only
 simp [G,bad,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record]
#print conflict
#print axioms conflict
end NMB_SnapshotConflict
