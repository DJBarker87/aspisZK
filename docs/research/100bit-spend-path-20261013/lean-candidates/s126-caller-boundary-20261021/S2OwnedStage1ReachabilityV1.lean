import S2OwnedStage1ModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.Reachability
open AspisS2OwnedStage1
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem first_decoded_success (ops : Ops) (pub : Public) (bytes proof : Slice U8)
    (k : Usize) (checkpoint : alloc.vec.Vec U8)
    (h : first_decoded ops pub bytes proof k=ok (.Ok checkpoint)) :
    ops.op2 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub bytes proof k () none=ok (.Ok checkpoint) := by
  unfold first_decoded observer at h
  simp only [bind_tc_ok] at h
  obtain ⟨r,hr,h⟩ := bind_success _ _ _ h
  cases r with
  | Ok value =>
    simp only [core.result.Result.map_err] at h
    cases h
    exact hr
  | Err e =>
    change (do let mapped ← ops.op10 e; ok (core.result.Result.Err mapped)) = ok (.Ok checkpoint) at h
    obtain ⟨mapped,hmapped,h⟩ := bind_success _ _ _ h
    cases h

/-- One enclosing emitted owned-tail success supplies its own snapshot,
decoded statement, same semantic-public projection and release-None verifier
execution. Decoder/statement/child success are conclusions, not premises.
SDK IO and child interpretations remain named Ops fields at this scope. -/
theorem tail_success (ops : Ops) (checkpointIn data checkpointOut : Slice U8)
    (h : owned_stage1_tail ops checkpointIn data=ok (.Ok (),checkpointOut)) :
    ∃ (publicData proofData : alloc.vec.Vec U8) (statement : Statement)
      (pub : Public) (selectedProof : Slice U8)
      (proofLength proofStart proofEnd : Usize) (checkedEnd : Option Usize) (splitByte : U8) (k : Usize)
      (checkpoint : alloc.vec.Vec U8),
      ops.op11=ok (.Ok publicData) ∧
      decode_public_statement_box ops (alloc.vec.Vec.deref publicData)=ok (.Ok statement) ∧
      ops.op12=ok (.Ok proofData) ∧
      ops.op3=ok proofLength ∧
      ops.op6=ok proofStart ∧
      lift (Usize.checked_add proofStart proofLength)=ok checkedEnd ∧
      ops.op1 checkedEnd solana_program_error.ProgramError.InvalidAccountData=ok (.Ok proofEnd) ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proofData {start:=proofStart,«end»:=proofEnd}=ok selectedProof ∧
      Slice.index_usize data 1#usize=ok splitByte ∧
      lift (UScalar.cast .Usize splitByte)=ok k ∧
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement=ok pub ∧
      first_decoded ops pub (alloc.vec.Vec.deref publicData) selectedProof k=ok (.Ok checkpoint) ∧
      ops.op2 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        pub (alloc.vec.Vec.deref publicData) selectedProof k () none=ok (.Ok checkpoint) ∧
      core.slice.Slice.copy_from_slice core.marker.CopyU8 checkpointIn
        (alloc.vec.Vec.deref checkpoint)=ok checkpointOut := by
  unfold owned_stage1_tail at h
  obtain ⟨publicRead,hpublicRead,h⟩ := bind_success _ _ _ h
  cases publicRead with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
    cases h
  | Ok publicReadValue =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
    obtain ⟨decoded,hdecoded,h⟩ := bind_success _ _ _ h
    cases decoded with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
      cases h
    | Ok decodedValue =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
      obtain ⟨validated,hvalidated,h⟩ := bind_success _ _ _ h
      cases validated with
      | Err e =>
        simp only [core.result.Result.map_err, owned_stage1_tail.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError, owned_stage1_tail.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
        cases h
      | Ok validatedValue =>
        simp only [core.result.Result.map_err, owned_stage1_tail.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError, owned_stage1_tail.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
        cases validatedValue
        obtain ⟨common,hcommon,h⟩ := bind_success _ _ _ h
        obtain ⟨encoded,hencoded,h⟩ := bind_success _ _ _ h
        cases encoded with
        | Err e =>
          simp only [core.result.Result.map_err, owned_stage1_tail.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError, owned_stage1_tail.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
          cases h
        | Ok encodedValue =>
          simp only [core.result.Result.map_err, owned_stage1_tail.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError, owned_stage1_tail.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
          obtain ⟨proofRead,hproofRead,h⟩ := bind_success _ _ _ h
          cases proofRead with
          | Err e =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
            cases h
          | Ok proofReadValue =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
            obtain ⟨proofLength,hproofLength,h⟩ := bind_success _ _ _ h
            obtain ⟨proofStart,hproofStart,h⟩ := bind_success _ _ _ h
            obtain ⟨checkedEnd,hcheckedEnd,h⟩ := bind_success _ _ _ h
            obtain ⟨proofEnd,hproofEnd,h⟩ := bind_success _ _ _ h
            cases proofEnd with
            | Err e =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
              cases h
            | Ok proofEndValue =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
              split at h
              · cases h
              ·
                obtain ⟨frame,hframe,h⟩ := bind_success _ _ _ h
                obtain ⟨different,hdifferent,h⟩ := bind_success _ _ _ h
                split at h
                · cases h
                ·
                  obtain ⟨tagOffset,htagOffset,h⟩ := bind_success _ _ _ h
                  obtain ⟨storedTag,hstoredTag,h⟩ := bind_success _ _ _ h
                  obtain ⟨tag,htag,h⟩ := bind_success _ _ _ h
                  split at h
                  · cases h
                  ·
                    obtain ⟨pub,hpub,h⟩ := bind_success _ _ _ h
                    obtain ⟨selected,hselected,h⟩ := bind_success _ _ _ h
                    obtain ⟨splitByte,hsplitByte,h⟩ := bind_success _ _ _ h
                    obtain ⟨k,hk,h⟩ := bind_success _ _ _ h
                    obtain ⟨child,hchild,h⟩ := bind_success _ _ _ h
                    cases child with
                    | Err e =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
                      cases h
                    | Ok childValue =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, bind_tc_ok] at h
                      split at h
                      · cases h
                      ·
                        obtain ⟨copied,hcopied,h⟩ := bind_success _ _ _ h
                        cases h
                        exact ⟨publicReadValue,proofReadValue,decodedValue,pub,selected,proofLength,proofStart,proofEndValue,checkedEnd,splitByte,k,childValue,
                          hpublicRead,hdecoded,hproofRead,hproofLength,hproofStart,hcheckedEnd,hproofEnd,hselected,hsplitByte,hk,hpub,hchild,
                          first_decoded_success ops pub _ _ k childValue hchild,hcopied⟩

#print axioms first_decoded_success
#print axioms tail_success
end AspisS2OwnedStage1.Reachability
