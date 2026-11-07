import NLQ_SnapshotFold
set_option autoImplicit false
noncomputable section
namespace NLQ_SnapshotData
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- At a returning data-read occurrence, equality with the ORIGINAL bytes and
its allocation guard follow from THIS snapshot, without address reasoning. -/
theorem returned (e : Entry) (ops : AdapterRw.Ops) (a lo hi : Nat) (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot a lo hi)=.ok (.Ok bytes)) :
 bytes=e.buffers (e.handles a).1 ∧
 ((e.buffers (e.handles a).1).val.length=lo ∨ (e.buffers (e.handles a).1).val.length=hi) := by
 obtain ⟨copied,stored,view⟩ := S2W.SnapshotJoin.data_success ops (e.snapshot a lo hi) bytes read
 change (if (e.buffers (e.handles a).1).val.length=lo ∨
   (e.buffers (e.handles a).1).val.length=hi then core.result.Result.Ok (e.buffers (e.handles a).1)
   else core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)=
   core.result.Result.Ok copied at stored
 split at stored
 · rename_i allowed
   have same := core.result.Result.Ok.inj stored
   subst copied
   exact ⟨view.symm,allowed⟩
 · cases stored
#check @returned
#print axioms returned
end NLQ_SnapshotData
