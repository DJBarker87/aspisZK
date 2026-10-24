import S2W_D189Entry
set_option autoImplicit false
noncomputable section
namespace AspisS6SdkPublicRead
open Aeneas Aeneas.Std Result
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory
open S2W_CommittedCheckpoint

/-- A successful actual owned read rules out the deferred snapshot error and
identifies the complete original native public buffer, including its length.
There is no snapshot-shape, length or buffer-identity hypothesis. -/
theorem public_read (e : Entry) (ops : AdapterRw.Ops) (pub : Slice U8)
    (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
      (e.snapshot 1 1880 1880) = ok (.Ok pub)) :
    pub = e.buffers (e.handles 1).1 ∧ pub.val.length = 1880 := by
  obtain ⟨copied,stored,view⟩ := S2W.SnapshotJoin.data_success ops
    (e.snapshot 1 1880 1880) pub read
  change (if (e.buffers (e.handles 1).1).val.length = 1880 ∨
      (e.buffers (e.handles 1).1).val.length = 1880 then
      core.result.Result.Ok (e.buffers (e.handles 1).1) else
      core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) =
        core.result.Result.Ok copied at stored
  split at stored
  · rename_i admitted
    have same := core.result.Result.Ok.inj stored
    subst copied
    have bytes := congrArg Subtype.val view
    have equal : pub = e.buffers (e.handles 1).1 := Subtype.ext bytes.symm
    refine ⟨equal,?_⟩
    rw [equal]
    exact admitted.elim id id
  · cases stored


#print axioms public_read
end AspisS6SdkPublicRead
