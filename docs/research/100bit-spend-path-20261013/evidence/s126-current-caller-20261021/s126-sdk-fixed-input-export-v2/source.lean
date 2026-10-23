import S126SdkFixedInputCurrentV1
import S126SdkLinkedCurrentV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ProofGate.FixedLinked

/-- The new result genuinely strengthens the previous statement, on the same
carriers/quantifiers and with exactly the same source decoder/current caller. -/
theorem forget_initial_inputs (initial : OwnedSdk) (ops : Ops)
    (verifierOps : AspisR1CurrentCaller.Ops)
    (facts : SourceLinkedFirst initial ops verifierOps) :
    Linked.SourceLinkedFirst ops verifierOps := by
  obtain ⟨proof,candidate,decoded,common,pub,suffix,k,cp,_,_,
    hd,hc,he,hr,hg,hfirst⟩ := facts
  exact ⟨proof,candidate,decoded,common,pub,suffix,k,cp,hd,hc,he,hr,hg,hfirst⟩

theorem gate_proof_length (proof : alloc.vec.Vec U8) (candidate : Array U8 688#usize)
    (gate : reference_gate (alloc.vec.Vec.deref proof) candidate=
      ok (.Ok (688#usize,58295#usize))) : proof.val.length=58295 := by
  have length : Slice.len (alloc.vec.Vec.deref proof)=58295#usize := by
    by_contra wrong
    have rejected := wrong_length_reject (alloc.vec.Vec.deref proof) candidate wrong
    cases rejected.symm.trans gate
  have value := congrArg UScalar.val length
  simpa [Slice.len,FrameOperationsTotal.deref_val] using value

/-- ACCEPTED-ONLY identity-bearing source/current-first witness for the lead.
The full 58295-byte account and its actual 57607-byte suffix are distinguished.
No external byte identity, child success, prefix, tag, clone or frame premise
is added to the enclosing installed caller execution. Native embedding and
TX2/cross-transaction facts remain outside this reference-layer theorem. -/
theorem owned_stage1_fixed_input_witness (ops : Ops)
    (verifierOps : AspisR1CurrentCaller.Ops) (program : Array U8 32#usize)
    (initial out : OwnedSdk) (instruction : alloc.vec.Vec U8)
    (accepted : owned_stage1 (Installation.install ops verifierOps)
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
        publicBytes proofSuffix split=ok (.Ok checkpoint) := by
  obtain ⟨proof,candidate,decoded,common,pub,suffix,k,cp,hproof,hpub,
    hd,_,_,hr,hgate,hfirst⟩ :=
      owned_stage1_source_linked_first ops verifierOps program initial out instruction accepted
  have length := gate_proof_length proof candidate hgate
  obtain ⟨selected,selectedRun,selectedVal,selectedLength⟩ :=
    FrameOperationsTotal.compact_suffix_total proof length
  have same := Result.ok.inj (selectedRun.symm.trans hr)
  subst suffix
  exact ⟨alloc.vec.Vec.deref proof,pub,selected,decoded,k,cp,hproof,hpub,
    (FrameOperationsTotal.deref_val proof ▸ length),selectedVal,selectedLength,hd,hfirst⟩

theorem borrowed_stage1_fixed_input_witness (ops : Ops)
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
        publicBytes proofSuffix split=ok (.Ok checkpoint) := by
  apply owned_stage1_fixed_input_witness ops verifierOps program initial out instruction
  rw [←BorrowedEquivalence.stage1_eq]
  exact accepted

#print axioms forget_initial_inputs
#print axioms gate_proof_length
#print axioms owned_stage1_fixed_input_witness
#print axioms borrowed_stage1_fixed_input_witness
end AspisS2OwnedStage1.SdkReference.ProofGate.FixedLinked
