import S6SdkReachedFirstV1
set_option autoImplicit false
namespace AspisS6SdkProofBuffer
open Aeneas Aeneas.Std Result
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_NativeConsolidation AspisS6CurrentFirstInstallation AspisS6CurrentVerifierCarrier
open AspisS6CurrentCodecInstallation AspisS6CurrentAdapterCarrier
/-- Exact same snapshot accessor, generalized to the actually selected account.
The source read proves both its complete buffer identity and admitted length. -/
theorem snapshot_read (e : Entry) (ops : AdapterRw.Ops) (account length : Nat) (pub : Slice U8)
    (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
      (e.snapshot account length length) = ok (.Ok pub)) :
    pub = e.buffers (e.handles account).1 ∧ pub.val.length = length := by
  obtain ⟨copied,stored,view⟩ := S2W.SnapshotJoin.data_success ops
    (e.snapshot account length length) pub read
  change (if (e.buffers (e.handles account).1).val.length = length ∨
      (e.buffers (e.handles account).1).val.length = length then
      core.result.Result.Ok (e.buffers (e.handles account).1) else
      core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) =
        core.result.Result.Ok copied at stored
  split at stored
  · rename_i admitted
    have same := core.result.Result.Ok.inj stored
    subst copied
    have bytes := congrArg Subtype.val view
    have equal : pub = e.buffers (e.handles account).1 := Subtype.ext bytes.symm
    refine ⟨equal,?_⟩
    rw [equal]
    exact admitted.elim id id
  · cases stored

#print axioms snapshot_read
end AspisS6SdkProofBuffer
