import S2E_Execution
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2F
open S2E_Reference.S2E_Reference AspisR1.S2E

/-- A rejected source shape does not call a child or enter SDK cleanup. -/
theorem stage1_shape_rejected {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (original : Original S) (error : PE)
    (rejected : shape1 ops original.data (alloc.vec.Vec.len original.sdk.accounts) = ok (.Err error)) :
    E ops children original = ok (.Err error,original.state,original.sdk) := by
  simp only [E,stage1,rejected,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Failed checkpoint acquisition owns no new guard. Earlier admission occurred;
no checkpoint/public continuation or newly acquired-guard cleanup is run. -/
theorem stage1_checkpoint_rejected {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (original : Original S) (account : OwnedAccount)
    (post : SDK) (guards : LiveGuards) (error : PE)
    (shape : shape1 ops original.data (alloc.vec.Vec.len original.sdk.accounts) = ok (.Ok ()))
    (admitted : admission ops original.program original.sdk = ok (.Ok ()))
    (read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) original.sdk.accounts 2#usize = ok account)
    (borrow : owned_acquire_checkpoint original.sdk {checkpoint:=none,«public»:=none,proof:=none}
      account.data_slot = ok (.Err error,post,guards)) :
    E ops children original = ok (.Err error,original.state,post) := by
  simp only [E,stage1,shape,admitted,read,borrow,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- A rejected checkpoint borrow in stage2 leaves the proof guard to the caller.
It performs no tail/second/emit call. This is local, not a native prefix theorem. -/
theorem stage2_checkpoint_rejected {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (state : S) (sdk post : SDK) (validated : Validated)
    (proofSlot : Usize) (account : OwnedAccount) (error : PE)
    (read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) sdk.accounts 6#usize = ok account)
    (borrow : owned_acquire_shared sdk account.data_slot = ok (.Err error,post)) :
    stage2_checkpoint ops children state sdk validated proofSlot = ok (.Err error,state,post) := by
  simp only [stage2_checkpoint,read,borrow,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Actual stage2 rejects the account count before all shape Ops and return-data
clearing. No rollback/abort claim is inferred from this ordinary Err equation. -/
theorem stage2_count_rejected {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (original : Original S)
    (badCount : alloc.vec.Vec.len original.sdk.accounts ≠ 7#usize) :
    stage2 ops children original.state original.sdk original.program original.data =
      ok (.Err solana_program_error.ProgramError.InvalidInstructionData,original.state,original.sdk) := by
  simp only [stage2,bne_iff_ne,badCount,if_true]

#print axioms stage1_shape_rejected
#print axioms stage1_checkpoint_rejected
#print axioms stage2_checkpoint_rejected
#print axioms stage2_count_rejected
end AspisR1.S2F
