/- UNCOMPILED CANDIDATE. Requires a reviewed, kernel-reconstructed closure.
No direct project trust imports. This file has not been elaborated. -/
import Port30JOIN_CheckedClosure
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace Port30JOIN
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_NativeConsolidation
open AspisR1.S2W_D189Consolidation AspisR1.S2W_AuthenticatedInputs
open AspisR1.S2W_InputSchedule AspisR1.S2W_ExpandedChildren AspisR1.S2W_TraceSplice
open AspisR1.MultiproofConeCanonical
theorem accepted_original_sdk_s2_s1 {W A E M Cv : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e : Entry) (e2 : Entry) (world world2 : W)
    (admission : S2W_D189Consolidation.RuntimeEntrypointAdmission L e world 3)
    (admission2 : S2W_D189Consolidation.RuntimeEntrypointAdmission L e2 world2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)

    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
      native1 native2 hashv)
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (sha256 H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (initial final : A) (post : Heap (Nat → Record))
    (accepted : AspisS6SdkFirstObjectEquivalence.originalFirst native1 copy allocator e program data initial =
      ok (.Ok (out,post,final)))
    (data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state2 final2 : A) (post2 : Heap (Nat → Record))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (port : S2W_ExpandedChildren.ChildConeJoin E (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)))
    (firstMarks : S2W_TraceSplice.FirstMarks port)
    (secondMarks : S2W_TraceSplice.SecondMarks port) :
    post = writeBracket e.heap 2 0 0 (source (nativeBytes out)) ∧
    S2W_AccountObservations.observe S2W_ReturnedCheckpoint.encode e.metadata 3 post 1 =
      S2W_D189Interpretation.nativeObserve L S2W_ReturnedCheckpoint.encode e.metadata 3 world e.heap.ambient 1 ∧
    ∃ (rawCut f : FirstCut) (s : SecondCut) selectedPublic outer pre middle fs ss,
      SourceCuts (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) e.first (e2.second secondSizes) out rawCut s ∧
      f = {rawCut with semantic := selectedPublic} ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        rawCut.statement = ok selectedPublic ∧
      SourceCuts (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) e.first (e2.second secondSizes) out f s ∧
      (∃ encoded,
        AspisS6CurrentCodecInstallation.decode f.pub = ok (.Ok f.statement) ∧
        AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 f.pub =
          ok (.Ok (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)) ∧
        AspisS6CurrentCodecInstallation.encode f.statement = ok (.Ok encoded) ∧ encoded.val = f.pub.val ∧
        f.split = AspisR1CurrentCaller.compact.SPLIT ∧
        AspisR1CurrentCaller.FirstComposition.firstCurrent
          AdapterRw.solana_program_error.ProgramError.InvalidAccountData (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
          (AspisS6CurrentVerifierCarrier.toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))))
          (fun error => adapterOps.op44 (AspisS6CurrentVerifierCarrier.fromError error)) f.pub f.proof f.split = ok (.Ok out)) ∧
      (f.pub = e.buffers (e.handles 1).1 ∧ f.pub.val.length = 1880 ∧
      payloadBytes S2W_ReturnedCheckpoint.encode (L.cellPayload world (L.accountData world 1))
        (L.cellPayload world (L.accountData world 1)).descriptor.length =
          MultiproofConeCanonical.bytesOf f.pub.val ∧
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual f.pub =
        ok (.Ok (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)) ∧
      f.split=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
        (sem : r1_semantic.Verified Unit) (prepared : AspisR1PublicPreparation.verifier.Prepared)
        (scratch : Array PE 29#usize),
        AspisR1SelectedWideViewV1.verifier.candidate.wide_view f.proof semantic y1=ok (.Ok v) ∧
        v.variant = .S2 ∧
        (semanticBase ops B).op9 (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement))) v.semantic () none=ok (.Ok sem) ∧
        AspisR1PublicPreparation.PreparedScratchModel.prepare
          (concreteBoundaries (installedBoundaries (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed))
          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) ()
          (mapArray retainedE (Array.repeat 29#usize zero)) = ok (.Ok prepared,scratch) ∧
        powersPublic 29#usize prepared.gamma = ok scratch ∧
        AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize (toClaimE prepared.gamma) = ok (mapArray toClaimE scratch) ∧
        BorrowedClaimPrepared.claim (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) (retainedSem sem) v.y1
          (AspisR1SelectedWideViewV1.prepCarrier v.inactive) scratch prepared.kappa = ok (.Ok prepared.claim) ∧
        AspisS1SemanticArrayRanges.CurrentVerifiedNumeric sem ∧
        AspisS1SemanticArrayRanges.CurrentVerifiedChallengesNumeric sem ∧
        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧
        OriginalPayloadClaimMeaning (retainedSem sem) v.y1
          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))
          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)
          (mapArray toClaimE scratch) ∧
        (∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
          Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
          Canonical value ∧ decode value=decode (toClaimE prepared.gamma)^i.val) ∧
        ExactSerializedRankTrace (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) p f.pub root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        Row31QueryProgramMeaning (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) (AspisR1SelectedWideViewV1.preparedView v) prepared ∧
        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) f.pub f.proof f.split () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out)) ∧
      S2W_ExpandedTrace.runExpanded (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) (children port)
        (S2W_Observation.two (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) program e.first data (e2.second secondSizes) data2 slot) [] =
        ok (.Ok out,S2W_ExpandedTrace.full (children port) outer) ∧
      S2W_D189Interpretation.runOwned (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
        (S2W_Observation.two (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) program e.first data (e2.second secondSizes) data2 slot) [] e.heap =
        ok (.Ok out,outer,e.heap) ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      post2 = e2.heap ∧
      before e e2 .tx1 = S2W_D189Interpretation.nativeObserve L encode e.metadata 3 world e.heap.ambient ∧
      before e e2 .tx2 = S2W_D189Interpretation.nativeObserve L encode e2.metadata 7 world2 e2.heap.ambient ∧
      ∀ (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),
      CheckpointWriterConeJoin (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) decode H f.semantic f.pub f.proof f.split →
      CheckpointReaderConeJoin (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) decode H s.pub s.proof s.checkpoint →
      S2X.CheckpointVersionBinding
        (payloadBytes encode (post.payload (e.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
      S2W_ChildJoins.S8StageConeJoin f.proof y1 →
      ∃ parsed,
        S2W_LeadInterface.S2CallerFacts
          (observation f s out nodes y1 pre middle fs ss (before e e2) (after e e2 post))
          (S2Z.Oracle.leadDigest (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))) () H (bytesOf f.proof.val) (bytesOf f.pub.val)
          (bytesOf out.val) parsed ∧
        (∀ site, (observation f s out nodes y1 pre middle fs ss (before e e2) (after e e2 post)).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) := by
  let installed := (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
  have wrapped : S2W_D189Wrappers.first native1 copy allocator e program data initial =
      ok (.Ok (out,post,final)) := by
    rw [AspisS6SdkFirstObjectEquivalence.first_eq_original]
    exact accepted
  obtain ⟨rawCut,s,outer,pre,middle,fs,ss,cuts,expanded,ownedFrame,layout,
      unchanged,frame1,frame2,_oldConditional⟩ :=
    S2W_D189Consolidation.accepted_run L sdk copy std allocator e e2 world world2
      admission admission2 installed native1 native2 hashv extraction sha256 H p1 syscall
      program data data2 slot initial state2 final final2 out post post2 wrapped accepted2
      port firstMarks secondMarks
  obtain ⟨written,frame,allS1⟩ :=
    AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace
      L sdk copy std allocator e world admission adapterOps ops B native1 native2 hashv extraction
      p root length program data out initial final post accepted
  obtain ⟨selectedPublic,selection,chosen,numeric⟩ :=
    allS1 (e2.second secondSizes) rawCut s cuts
  let f : FirstCut := {rawCut with semantic := selectedPublic}
  obtain ⟨_,_,allSdk⟩ := AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts
    L sdk copy std allocator e world admission adapterOps
    (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
    native1 native2 hashv extraction program data initial final out post accepted
  obtain ⟨_,_,_,_,_,_,codec⟩ := allSdk (e2.second secondSizes) f s chosen
  refine ⟨written,frame,rawCut,f,s,selectedPublic,outer,pre,middle,fs,ss,
    cuts,rfl,selection,chosen,codec,numeric,expanded,ownedFrame,layout,
    unchanged,frame1,frame2,?_⟩
  intro decode nodes y1 writer reader history p2prime entry multiproof scan
  obtain ⟨owned1,_⟩ := S2W_D189Wrappers.first_accepted native1 copy std allocator
    e program data initial final out post wrapped
  have source1 := (extraction.stage1 program e.first data).symm.trans owned1
  have destinationSize := S2W_D189Entry.checkpoint_size e installed program data out source1
  have versionAtWrite : S2X.CheckpointVersionBinding
      (payloadBytes encode ((writeBracket e.heap 2 0 0 (source (nativeBytes out))).payload
        (e.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) := by
    rw [← written]; exact history
  obtain ⟨_,⟨version⟩⟩ := returned_committed e.heap 2 0 0 out (bytesOf s.checkpoint.val)
    rfl rfl destinationSize (writer.size out chosen.first) versionAtWrite
  obtain ⟨parsed,partialFacts⟩ := S2W_InputSchedule.input_schedule installed H
    e.first (e2.second secondSizes) f s out chosen decode nodes y1
    writer reader version p2prime entry multiproof scan
    (S2W_DigestExtraction.native_oracle installed native1 native2 hashv extraction sha256 H p1 syscall)
    pre middle fs ss (S2W_D189Consolidation.before e e2) (S2W_D189Consolidation.after e e2 post)
  have frames := S2W_D189Consolidation.wrapper_frames e e2 installed program data out source1 post written
  refine ⟨parsed,?_,?_⟩
  · apply (S2W_TwoFieldAudit.full_fields_iff _ installed H _ _ _ parsed partialFacts).2
    exact ⟨fun site _ a allowed => frames.1 site a allowed,fun _ => frames.2⟩
  · intro site
    rw [layout]
    rfl

#print axioms accepted_original_sdk_s2_s1
end Port30JOIN
end
