import S126SdkSizedAccountExportV1
import S2SdkFixedImageFirstV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.CheckpointWriter
open ProofGate.FixedLinked

/-- Same full installed caller execution supplies fixed original inputs,
source-current-first, the sized final-account checkpoint, all metadata, and
exactly one update of the complete byte-vector heap. ACCEPTED-ONLY reference
closure; native/source/runtime/oracle and cross-TX transport remain. -/
theorem borrowed_stage1_sized_account_image (ops : Ops)
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
      out.accounts=initial.accounts ∧ out.lamports_cells=initial.lamports_cells ∧
      ∃ account : OwnedAccount,
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
          initial.accounts 2#usize=ok account ∧
        BorrowedBufferFrame.buffers out=
          (BorrowedBufferFrame.buffers initial).set account.data_slot.val checkpoint := by
  obtain ⟨proof,pub,suffix,decoded,k,cp,hproof,hpub,length,range,suffixLength,
    hdecode,hcurrent,saved,size,accounts,lamports⟩ :=
      borrowed_stage1_sized_saved_account ops verifierOps program initial out instruction accepted
  obtain ⟨_,_,_,_,_,_,cp2,account,accountRead,_,_,_,_,_,_,_,stored,image⟩ :=
    borrowed_stage1_fixed_image_first ops verifierOps program initial out instruction accepted
  have actual : inputBytes out 2#usize=ok (alloc.vec.Vec.deref cp2) := by
    simp only [inputBytes,accounts,accountRead,stored,bind_tc_ok]
  have sameSlice := Result.ok.inj (actual.symm.trans saved)
  have same : cp2=cp := by
    apply Subtype.ext
    have values := congrArg (fun s : Slice U8 => s.val) sameSlice
    simpa only [FrameOperationsTotal.deref_val] using values
  subst cp2
  exact ⟨proof,pub,suffix,decoded,k,cp,hproof,hpub,length,range,suffixLength,
    hdecode,hcurrent,saved,size,accounts,lamports,account,accountRead,image⟩

#print axioms borrowed_stage1_sized_account_image
end AspisS2OwnedStage1.SdkReference.CheckpointWriter
