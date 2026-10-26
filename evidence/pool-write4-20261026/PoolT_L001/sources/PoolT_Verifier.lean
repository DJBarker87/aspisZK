import Hist_CommittedPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolT_Verifier
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory
open MultiproofConeCanonical

/-- Derive returned size from the original owned call and its same account2
snapshot. No successful child or independently chosen saved-size premise. -/
theorem returned_size (ops : AdapterRw.Ops) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e.first data = ok (.Ok saved)) :
    saved.val.length = 1768 := by
  obtain ⟨ca,bytes,ic,read,len⟩ := AdapterRw.Cuts.stage1_checkpoint_length ops program e.first data saved accepted
  have eqc := Result.ok.inj (ic.symm.trans (first_index e).2.2)
  subst ca
  obtain ⟨copied,stored,same⟩ := S2W.SnapshotJoin.data_success ops (e.snapshot 2 1768 1768) bytes read
  change (if (e.buffers (e.handles 2).1).val.length = 1768 ∨
      (e.buffers (e.handles 2).1).val.length = 1768 then core.result.Result.Ok (e.buffers (e.handles 2).1)
      else core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) =
      core.result.Result.Ok copied at stored
  split at stored
  · have hc := core.result.Result.Ok.inj stored
    subst copied
    have hs := checkpoint_size e ops program data saved accepted
    change (e.buffers (e.handles 2).1).val.length = 1768 at hs
    have lens : saved.val.length = bytes.val.length := by
      exact congrArg UScalar.val len
    rw [same] at lens
    exact lens.trans hs
  · cases stored

#print axioms returned_size
end AspisR1.PoolT_Verifier
end
