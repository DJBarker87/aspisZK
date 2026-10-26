import PoolT_Event
import AdapterRwAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolT_Snapshot
open Aeneas Aeneas.Std Result S2W_D189Entry

/-- Successful reads of the existing native wrapper snapshot are the original
pre-call buffer. No independently supplied byte equality or successful clone. -/
theorem data (ops : AdapterRw.Ops) (e : Entry) (slot first second : Nat) (bytes : Slice U8)
    (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot slot first second) = ok (.Ok bytes)) :
    bytes = (e.buffers (e.handles slot).1).deref ∧
      ((e.buffers (e.handles slot).1).val.length = first ∨
       (e.buffers (e.handles slot).1).val.length = second) := by
  obtain ⟨copied,stored,same⟩ := S2W.SnapshotJoin.data_success ops _ bytes read
  change (if (e.buffers (e.handles slot).1).val.length = first ∨
      (e.buffers (e.handles slot).1).val.length = second then core.result.Result.Ok (e.buffers (e.handles slot).1)
      else core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) =
      core.result.Result.Ok copied at stored
  split at stored
  · rename_i lengths
    have eq := core.result.Result.Ok.inj stored
    subst copied
    exact ⟨same.symm,lengths⟩
  · cases stored

#print axioms data
end AspisR1.PoolT_Snapshot
end
