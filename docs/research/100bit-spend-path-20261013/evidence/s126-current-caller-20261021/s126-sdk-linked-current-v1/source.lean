import S2SdkLinkedCallerV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ProofGate.Linked

/-- Actual source decoder and candidate encoder, exact admitted original proof
buffer/suffix and current first wrapper, all retained in one execution witness. -/
def SourceLinkedFirst (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops) : Prop :=
  ∃ (proofData : alloc.vec.Vec U8) (candidate : Array U8 688#usize)
    (decoded : AspisR1TerminalDecoder.PublicBinding.Statement) (common : Common)
    (publicBytes proofBytes : Slice U8) (split : Usize) (checkpoint : alloc.vec.Vec U8),
    AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual publicBytes=ok (.Ok decoded) ∧
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
      (SourceInstallation.fromDecoderStatement decoded)=ok common ∧
    SourceInstallation.actualEncoder common.lane_transition.candidate_afterstate=ok (.Ok candidate) ∧
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proofData {start:=688#usize,«end»:=58295#usize}=ok proofBytes ∧
    reference_gate (alloc.vec.Vec.deref proofData) candidate=
      ok (core.result.Result.Ok (688#usize,58295#usize)) ∧
    AspisR1CurrentCaller.FirstComposition.firstCurrent
      solana_program_error.ProgramError.InvalidAccountData verifierOps
      (SourceInstallation.currentDigest
        (SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)))
      (fun e => ops.op11 (SourceInstallation.freshError e)) publicBytes proofBytes split=ok (.Ok checkpoint)

private theorem decoded_current (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (statement : Statement) (pub : AspisS2OwnedStage1.Reachability.Public)
    (bytes proof : Slice U8) (k : Usize) (cp : alloc.vec.Vec U8)
    (hbox : decode_public_statement_box (Installation.install ops verifierOps) bytes=ok (.Ok statement))
    (hpub : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      statement=ok pub)
    (hfirst : first_decoded (Installation.install ops verifierOps) pub bytes proof k=ok (.Ok cp)) :
    ∃ (decoded : AspisR1TerminalDecoder.PublicBinding.Statement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok decoded) ∧
      statement=SourceInstallation.fromDecoderStatement decoded ∧
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

/-- ACCEPTED-ONLY complete installed owned caller. One enclosing execution
supplies actual decoding, same-statement candidate encoding, same-buffer gate
and same-bytes current first call. No child success or candidate/parse match is
an independent premise. Native SDK/runtime correspondence remains separate. -/
theorem owned_stage1_source_linked_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : owned_stage1 (Installation.install ops verifierOps) program sdk data=ok (.Ok (),sdkOut)) :
    SourceLinkedFirst ops verifierOps := by
  obtain ⟨proofData,candidate,statement,common,pub,bytes,proof,k,cp,
    hbox,hcommon,hpub,hencode,hrange,hfirst,hgate,_⟩ :=
      owned_stage1_linked_first ops verifierOps program sdk sdkOut data accepted
  obtain ⟨decoded,hdecode,statementEq,hcurrent⟩ :=
    decoded_current ops verifierOps statement pub bytes proof k cp hbox hpub hfirst
  change SourceInstallation.actualEncoder common.lane_transition.candidate_afterstate=
    ok (.Ok candidate) at hencode
  rw [statementEq] at hcommon
  exact ⟨proofData,candidate,decoded,common,bytes,proof,k,cp,
    hdecode,hcommon,hencode,hrange,hgate,hcurrent⟩

/-- Consume the complete borrowed-reference/owned equality, including reverse
release, in this same shared decoder/encoder/gate/current-first witness. -/
theorem borrowed_stage1_source_linked_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
      program sdk data=ok (.Ok (),sdkOut)) :
    SourceLinkedFirst ops verifierOps := by
  apply owned_stage1_source_linked_first ops verifierOps program sdk sdkOut data
  rw [←BorrowedEquivalence.stage1_eq]
  exact accepted

#print axioms owned_stage1_source_linked_first
#print axioms borrowed_stage1_source_linked_first
end AspisS2OwnedStage1.SdkReference.ProofGate.Linked
