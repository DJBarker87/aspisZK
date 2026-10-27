import RPz8_SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SnapshotRead
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry

/-- Successful owned snapshot reads expose the ORIGINAL entry buffer,
including a derived admitted length, without a post-state equality premise. -/
theorem buffer (e : Entry) (ops : AdapterRw.Ops) (a len1 len2 : Nat) (data : Slice U8)
    (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
      (e.snapshot a len1 len2) = ok (.Ok data)) :
    data.val = (e.buffers (e.handles a).1).val ∧
      ((e.buffers (e.handles a).1).val.length = len1 ∨
       (e.buffers (e.handles a).1).val.length = len2) := by
  obtain ⟨copied,stored,view⟩ := S2W.SnapshotJoin.data_success ops _ data read
  change (if (e.buffers (e.handles a).1).val.length = len1 ∨
      (e.buffers (e.handles a).1).val.length = len2 then
      core.result.Result.Ok (e.buffers (e.handles a).1)
      else core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) =
    core.result.Result.Ok copied at stored
  split at stored
  · rename_i size
    have same := core.result.Result.Ok.inj stored
    exact ⟨(congrArg (fun d : Slice U8 => d.val) view).symm.trans
      (congrArg (fun d : Slice U8 => d.val) same).symm,size⟩
  · cases stored

#print axioms buffer
end AspisR1.SCE_SnapshotRead
end
