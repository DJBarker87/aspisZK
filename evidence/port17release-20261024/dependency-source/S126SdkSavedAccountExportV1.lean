import S126SdkFixedSavedCurrentV1
import S2SdkMetadataFrameV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.CheckpointWriter
open ProofGate.FixedLinked

/-- Read the SAME saved checkpoint through the final account2 descriptor.
Account/lamport preservation is derived from this enclosing execution, not an
extra descriptor-stability or writer premise. ACCEPTED-ONLY reference layer. -/
theorem borrowed_stage1_saved_account (ops : Ops)
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
      out.accounts=initial.accounts ∧ out.lamports_cells=initial.lamports_cells := by
  obtain ⟨proof,pub,suffix,decoded,k,cp,account,proofOrigin,publicOrigin,
    accountRead,length,suffixVal,suffixLength,hdecode,hcurrent,saved⟩ :=
      borrowed_stage1_fixed_saved_current ops verifierOps program initial out instruction accepted
  have accounts := MetadataFrame.borrowed_accounts_preserved
    (Installation.install ops verifierOps) program initial out instruction (.Ok ()) accepted
  have lamports := MetadataFrame.borrowed_lamports_preserved
    (Installation.install ops verifierOps) program initial out instruction (.Ok ()) accepted
  refine ⟨proof,pub,suffix,decoded,k,cp,proofOrigin,publicOrigin,length,suffixVal,
    suffixLength,hdecode,hcurrent,?_,accounts,lamports⟩
  simp only [inputBytes,accounts,accountRead,saved,bind_tc_ok]

#print axioms borrowed_stage1_saved_account
end AspisS2OwnedStage1.SdkReference.CheckpointWriter
