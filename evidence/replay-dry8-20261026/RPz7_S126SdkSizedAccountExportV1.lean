import RPz7_S126SdkSavedAccountExportV1
import RPz7_S2SdkSizedSavedFirstV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.CheckpointWriter
open ProofGate.FixedLinked

/-- Any successful final account2 view has the caller-derived S2 size1768.
No checkpoint size, writer or child-success premise is added to the run. -/
theorem borrowed_stage1_checkpoint_length (ops : Ops) (program : Array U8 32#usize)
    (initial out : OwnedSdk) (data : alloc.vec.Vec U8)
    (verifierOps : AspisR1CurrentCaller.Ops)
    (accepted : BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
      program initial data=ok (.Ok (),out))
    (bytes : Slice U8) (read : inputBytes out 2#usize=ok bytes) : bytes.val.length=1768 := by
  obtain ⟨_,_,_,_,cp,account,accountRead,_,saved,length⟩ :=
    borrowed_stage1_sized_saved_first ops verifierOps program initial out data accepted
  have accounts := MetadataFrame.borrowed_accounts_preserved
    (Installation.install ops verifierOps) program initial out data (.Ok ()) accepted
  have actual : inputBytes out 2#usize=ok (alloc.vec.Vec.deref cp) := by
    simp only [inputBytes,accounts,accountRead,saved,bind_tc_ok]
  have same := congrArg (fun s : Slice U8 => s.val.length) (Result.ok.inj (actual.symm.trans read))
  simpa only [FrameOperationsTotal.deref_val,length] using same.symm

/-- Complete reference-layer fixed-input/current-first/writer/size/metadata
join. The single complete accepted installed caller is its only premise.
Actual SDK/source/runtime and cross-transaction transport remain separate. -/
theorem borrowed_stage1_sized_saved_account (ops : Ops)
    (verifierOps : AspisR1CurrentCaller.Ops) (program : Array U8 32#usize)
    (initial out : OwnedSdk) (instruction : alloc.vec.Vec U8)
    (accepted : BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
      program initial instruction=ok (.Ok (),out)) :
    ∃ (proofAccount publicBytes proofSuffix : Slice U8)
      (decoded : AspisR1TerminalDecoder.PublicBinding.Statement)
      (split : Usize) (checkpoint : alloc.vec.Vec U8),
      inputBytes initial 0#usize=ok proofAccount ∧
      inputBytes initial 1#usize=ok publicBytes ∧
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
      inputBytes out 2#usize=ok (alloc.vec.Vec.deref checkpoint) ∧
      checkpoint.val.length=1768 ∧
      out.accounts=initial.accounts ∧ out.lamports_cells=initial.lamports_cells := by
  obtain ⟨proof,pub,suffix,decoded,k,cp,hproof,hpub,length,range,suffixLength,
    hdecode,hcurrent,saved,accounts,lamports⟩ :=
      borrowed_stage1_saved_account ops verifierOps program initial out instruction accepted
  have size := borrowed_stage1_checkpoint_length ops program initial out instruction verifierOps
    accepted (alloc.vec.Vec.deref cp) saved
  exact ⟨proof,pub,suffix,decoded,k,cp,hproof,hpub,length,range,suffixLength,
    hdecode,hcurrent,saved,(FrameOperationsTotal.deref_val cp ▸ size),accounts,lamports⟩

#print axioms borrowed_stage1_checkpoint_length
#print axioms borrowed_stage1_sized_saved_account
end AspisS2OwnedStage1.SdkReference.CheckpointWriter
