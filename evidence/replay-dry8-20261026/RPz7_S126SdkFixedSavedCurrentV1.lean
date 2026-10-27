import RPz7_S2SdkFixedSavedFirstV1
import RPz7_S126SdkFixedInputCurrentV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.CheckpointWriter
open ProofGate.FixedLinked

-- Same checked decoder/current-first application as FixedInputCurrentV1; all
-- parsing/projection/reuse/observer/tx1 facts below use their existing owners.
private theorem same_decoded_current (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (statement : AspisS2OwnedStage1.Reachability.Statement) (pub : AspisS2OwnedStage1.Reachability.Public)
    (bytes proof : Slice U8) (k : Usize) (cp : alloc.vec.Vec U8)
    (hbox : decode_public_statement_box (Installation.install ops verifierOps) bytes=ok (.Ok statement))
    (hpub : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      statement=ok pub)
    (hfirst : first_decoded (Installation.install ops verifierOps) pub bytes proof k=ok (.Ok cp)) :
    ∃ (decoded : AspisR1TerminalDecoder.PublicBinding.Statement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok decoded) ∧
      statement=CurrentCarrier.fromDecoderStatement decoded ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        solana_program_error.ProgramError.InvalidAccountData verifierOps
        (SourceInstallation.currentDigest
          (SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)))
        (fun e => ops.op11 (SourceInstallation.freshError e)) bytes proof k=ok (.Ok cp) := by
  rw [Installation.boxed_eq] at hbox
  have hactual := SourceInstallation.boxed_success
    (Installation.legacyHelperOps (Installation.install ops verifierOps)) bytes statement hbox
  change SourceInstallation.actualDecoder bytes=ok (.Ok statement) at hactual
  obtain ⟨decoded,hdecode,hstatement⟩ := SourceInstallation.decoder_success bytes statement hactual
  refine ⟨decoded,hdecode,hstatement,?_⟩
  subst statement
  rw [DecodedReuse.semantic_public_eq] at hpub
  have selection : CurrentCarrier.toCurrentPublic pub=
      AspisR1CurrentCaller.FirstComposition.toCurrentPublic
        (AspisR1PublicPreparation.PreparationBinding.preparationPublic decoded) := by
    have projected := CurrentCarrier.selected_public decoded
    rw [hpub] at projected
    exact Result.ok.inj projected
  have htx := Installation.first_success ops verifierOps pub bytes proof k cp hfirst
  rw [selection] at htx
  unfold AspisR1CurrentCaller.FirstComposition.firstCurrent
  rw [AspisR1PublicPreparation.RepinS6First.reuse_decoded _ _ _ _ _ _ _ hdecode]
  unfold AspisR1PublicPreparation.RepinS6First.first_decoded
    AspisR1PublicPreparation.RepinS6First.observer
    AspisR1CurrentCaller.FirstComposition.currentTx1
  simp only [bind_tc_ok,Option.map_none,htx,
    AspisR1PublicPreparation.core.result.Result.map_err]


/-- The checkpoint returned by the actual current first wrapper is the same
checkpoint saved at the original account2 slot after full owned finalization.
Fixed initial proof/public and exact compact suffix are conclusions of the
one enclosing installed caller execution. ACCEPTED-ONLY reference layer. -/
theorem owned_stage1_fixed_saved_current (ops : Ops)
    (verifierOps : AspisR1CurrentCaller.Ops) (program : Array U8 32#usize)
    (initial out : OwnedSdk) (instruction : alloc.vec.Vec U8)
    (accepted : owned_stage1 (Installation.install ops verifierOps)
      program initial instruction=ok (.Ok (),out)) :
    ∃ (proofAccount publicBytes proofSuffix : Slice U8)
      (decoded : AspisR1TerminalDecoder.PublicBinding.Statement)
      (split : Usize) (checkpoint : alloc.vec.Vec U8) (account : OwnedAccount),
      inputBytes initial 0#usize=ok proofAccount ∧
      inputBytes initial 1#usize=ok publicBytes ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
        initial.accounts 2#usize=ok account ∧
      proofAccount.val.length=58295 ∧
      proofSuffix.val=(proofAccount.val.drop 688).take 57607 ∧
      proofSuffix.val.length=57607 ∧
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual publicBytes=ok (.Ok decoded) ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        solana_program_error.ProgramError.InvalidAccountData verifierOps
        (SourceInstallation.currentDigest
          (SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)))
        (fun e => ops.op11 (SourceInstallation.freshError e))
        publicBytes proofSuffix split=ok (.Ok checkpoint) ∧
      BorrowedBufferFrame.readBytes out account.data_slot=ok checkpoint := by
  obtain ⟨proof,statement,pub,bytes,suffix,k,cp,account,
    accountRead,proofOrigin,publicOrigin,hbox,hpub,length,range,hfirst,saved⟩ :=
      owned_stage1_fixed_saved_first ops verifierOps program initial out instruction accepted
  obtain ⟨decoded,hdecode,_,hcurrent⟩ :=
    same_decoded_current ops verifierOps statement pub bytes suffix k cp hbox hpub hfirst
  obtain ⟨selected,selectedRun,selectedVal,selectedLength⟩ :=
    FrameOperationsTotal.compact_suffix_total proof length
  have same := Result.ok.inj (selectedRun.symm.trans range)
  subst suffix
  exact ⟨alloc.vec.Vec.deref proof,bytes,selected,decoded,k,cp,account,
    proofOrigin,publicOrigin,accountRead,(FrameOperationsTotal.deref_val proof ▸ length),
    selectedVal,selectedLength,hdecode,hcurrent,saved⟩

/-- Complete borrowed caller, including errors and guard finalization, is the
already checked same Result/state function. No extra writer premise added. -/
theorem borrowed_stage1_fixed_saved_current (ops : Ops)
    (verifierOps : AspisR1CurrentCaller.Ops) (program : Array U8 32#usize)
    (initial out : OwnedSdk) (instruction : alloc.vec.Vec U8)
    (accepted : BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
      program initial instruction=ok (.Ok (),out)) :
    ∃ (proofAccount publicBytes proofSuffix : Slice U8)
      (decoded : AspisR1TerminalDecoder.PublicBinding.Statement)
      (split : Usize) (checkpoint : alloc.vec.Vec U8) (account : OwnedAccount),
      inputBytes initial 0#usize=ok proofAccount ∧
      inputBytes initial 1#usize=ok publicBytes ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
        initial.accounts 2#usize=ok account ∧
      proofAccount.val.length=58295 ∧
      proofSuffix.val=(proofAccount.val.drop 688).take 57607 ∧
      proofSuffix.val.length=57607 ∧
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual publicBytes=ok (.Ok decoded) ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        solana_program_error.ProgramError.InvalidAccountData verifierOps
        (SourceInstallation.currentDigest
          (SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)))
        (fun e => ops.op11 (SourceInstallation.freshError e))
        publicBytes proofSuffix split=ok (.Ok checkpoint) ∧
      BorrowedBufferFrame.readBytes out account.data_slot=ok checkpoint := by
  apply owned_stage1_fixed_saved_current ops verifierOps program initial out instruction
  rw [←BorrowedEquivalence.stage1_eq]
  exact accepted

#print axioms owned_stage1_fixed_saved_current
#print axioms borrowed_stage1_fixed_saved_current
end AspisS2OwnedStage1.SdkReference.CheckpointWriter
