import S2E_Execution
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2F
open S2E_Reference.S2E_Reference AspisR1.S2E

/-- Inverts the actual extracted stage2 body. Shape operations stay opaque;
clear/validate/drop are obtained from this one execution, with their states. -/
theorem stage2_prefix {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (original : Original S) (finalState : S) (finalSdk : SDK)
    (accepted : stage2 ops children original.state original.sdk original.program original.data =
      ok (.Ok (),finalState,finalSdk)) :
    ∃ cleared validatedState validated beforeDrop,
      children.clear_return_data original.state = ok cleared ∧
      children.validate_asq8 cleared original.program original.sdk original.data =
        ok (.Ok validated,validatedState) ∧
      stage2_proof ops children validatedState original.sdk validated =
        ok (.Ok (),beforeDrop,finalSdk) ∧
      children.drop_statement beforeDrop validated.statement = ok finalState := by
  unfold stage2 at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨leading,hprefix,rest⟩ := bind_success _ _ _ accepted
    obtain ⟨magic,hmagic,rest⟩ := bind_success _ _ _ rest
    obtain ⟨magicSlice,hmagicSlice,rest⟩ := bind_success _ _ _ rest
    obtain ⟨mismatch,hmismatch,rest⟩ := bind_success _ _ _ rest
    cases mismatch with
    | true => cases rest
    | false =>
      obtain ⟨cleared,hclear,rest⟩ := bind_success (children.clear_return_data original.state) _ _ rest
      obtain ⟨⟨reply,validatedState⟩,hvalidate,rest⟩ := bind_success
        (children.validate_asq8 cleared original.program original.sdk original.data) _ _ rest
      cases reply with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame] at rest
        cases rest
      | Ok validated =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
        obtain ⟨⟨result,beforeDrop,sdk1⟩,hbody,rest⟩ := bind_success
          (stage2_proof ops children validatedState original.sdk validated) _ _ rest
        obtain ⟨afterDrop,hdrop,rest⟩ := bind_success
          (children.drop_statement beforeDrop validated.statement) _ _ rest
        cases rest
        exact ⟨cleared,validatedState,validated,beforeDrop,hclear,hvalidate,hbody,hdrop⟩

/-- Actual proof guard and its cleanup surround stage2's checkpoint continuation. -/
theorem stage2_proof_cut {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (state finalState : S) (sdk finalSdk : SDK) (validated : Validated)
    (accepted : stage2_proof ops children state sdk validated = ok (.Ok (),finalState,finalSdk)) :
    ∃ account acquired beforeDrop,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) sdk.accounts 0#usize = ok account ∧
      owned_acquire_shared sdk account.data_slot = ok (.Ok (),acquired) ∧
      stage2_checkpoint ops children state acquired validated account.data_slot = ok (.Ok (),finalState,beforeDrop) ∧
      release_shared beforeDrop account.data_slot = ok finalSdk := by
  unfold stage2_proof at accepted
  obtain ⟨account,hread,rest⟩ := bind_success _ _ _ accepted
  obtain ⟨⟨reply,acquired⟩,hacquire,rest⟩ := bind_success (owned_acquire_shared sdk account.data_slot) _ _ rest
  cases reply with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame] at rest
    cases rest
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
    obtain ⟨⟨result,state1,beforeDrop⟩,hbody,rest⟩ := bind_success
      (stage2_checkpoint ops children state acquired validated account.data_slot) _ _ rest
    obtain ⟨released,hdrop,rest⟩ := bind_success (release_shared beforeDrop account.data_slot) _ _ rest
    cases rest
    exact ⟨account,acquired,beforeDrop,hread,hacquire,hbody,hdrop⟩

/-- The checkpoint guard remains live through the tail, including emit_result. -/
theorem stage2_checkpoint_cut {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (state finalState : S) (sdk finalSdk : SDK)
    (validated : Validated) (proofSlot : Usize)
    (accepted : stage2_checkpoint ops children state sdk validated proofSlot = ok (.Ok (),finalState,finalSdk)) :
    ∃ account acquired,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) sdk.accounts 6#usize = ok account ∧
      owned_acquire_shared sdk account.data_slot = ok (.Ok (),acquired) ∧
      stage2_tail ops children state acquired validated proofSlot account.data_slot = ok (.Ok (),finalState) ∧
      release_shared acquired account.data_slot = ok finalSdk := by
  unfold stage2_checkpoint at accepted
  obtain ⟨account,hread,rest⟩ := bind_success _ _ _ accepted
  obtain ⟨⟨reply,acquired⟩,hacquire,rest⟩ := bind_success (owned_acquire_shared sdk account.data_slot) _ _ rest
  cases reply with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame] at rest
    cases rest
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
    obtain ⟨⟨result,state1⟩,hbody,rest⟩ := bind_success
      (stage2_tail ops children state acquired validated proofSlot account.data_slot) _ _ rest
    obtain ⟨released,hdrop,rest⟩ := bind_success (release_shared acquired account.data_slot) _ _ rest
    cases rest
    exact ⟨account,acquired,hread,hacquire,hbody,hdrop⟩

/-- Every successful stage2 tail gets public/proof/checkpoint arguments and
both child states from the same continuation. Constants remain Ops until G
installs their concrete interpretations. -/
theorem stage2_tail_cut {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (state finalState : S) (sdk : SDK)
    (validated : Validated) (proofSlot cpSlot : Usize)
    (accepted : stage2_tail ops children state sdk validated proofSlot cpSlot = ok (.Ok (),finalState)) :
    ∃ proofCell checkedEnd endOffset publicBytes encodedState expectedLength selected cpCell secondState,
      lift (Usize.checked_add 688#usize validated.proof_length) = ok checkedEnd ∧
      ops.op2 checkedEnd solana_program_error.ProgramError.InvalidAccountData = ok (.Ok endOffset) ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) sdk.data_cells proofSlot = ok proofCell ∧
      alloc.vec.Vec.len proofCell.bytes = endOffset ∧
      children.«public» state validated.statement = ok (.Ok publicBytes,encodedState) ∧
      ops.op12 = ok expectedLength ∧
      alloc.vec.Vec.len publicBytes = expectedLength ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proofCell.bytes {start:=688#usize,«end»:=endOffset} = ok selected ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) sdk.data_cells cpSlot = ok cpCell ∧
      children.second encodedState publicBytes.deref selected cpCell.bytes.deref = ok (.Ok (),secondState) ∧
      children.emit secondState validated.statement = ok (.Ok (),finalState) := by
  unfold stage2_tail at accepted
  obtain ⟨proofCell,hproof,rest⟩ := bind_success _ _ _ accepted
  obtain ⟨checked,hchecked,rest⟩ := bind_success _ _ _ rest
  obtain ⟨reply,hend,rest⟩ := bind_success _ _ _ rest
  cases reply with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at rest
    cases rest
  | Ok endOffset =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
    try dsimp only at rest
    split at rest
    · cases rest
    · rename_i lengthMatch
      obtain ⟨⟨publicReply,encodedState⟩,hpublic,rest⟩ := bind_success
        (children.«public» state validated.statement) _ _ rest
      cases publicReply with
      | Err error =>
        simp only [S2E_Reference.core.result.Result.map_err,
          stage2_tail.closure.Insts.CoreOpsFunctionFnOnceTupleProgramErrorProgramError,
          stage2_tail.closure.Insts.CoreOpsFunctionFnOnceTupleProgramErrorProgramError.call_once,
          core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at rest
        cases rest
      | Ok publicBytes =>
        simp only [S2E_Reference.core.result.Result.map_err,
          core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
        obtain ⟨expectedLength,hexpected,rest⟩ := bind_success ops.op12 _ _ rest
        try dsimp only at rest
        split at rest
        · cases rest
        · rename_i publicLengthMatch
          obtain ⟨selected,hrange,rest⟩ := bind_success _ _ _ rest
          obtain ⟨cpCell,hcp,rest⟩ := bind_success _ _ _ rest
          obtain ⟨⟨secondReply,secondState⟩,hsecond,rest⟩ := bind_success
            (children.second encodedState publicBytes.deref selected cpCell.bytes.deref) _ _ rest
          cases secondReply with
          | Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at rest
            cases rest
          | Ok unit =>
            cases unit
            try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
            have hl : alloc.vec.Vec.len proofCell.bytes = endOffset := by simpa only [bne_iff_ne,not_not] using lengthMatch
            have hp : alloc.vec.Vec.len publicBytes = expectedLength := by simpa only [bne_iff_ne,not_not] using publicLengthMatch
            exact ⟨proofCell,checked,endOffset,publicBytes,encodedState,expectedLength,selected,cpCell,secondState,
              hchecked,hend,hproof,hl,hpublic,hexpected,hp,hrange,hcp,hsecond,rest⟩

#print axioms stage2_tail_cut

#print axioms stage2_prefix
#print axioms stage2_proof_cut
#print axioms stage2_checkpoint_cut
end AspisR1.S2F
