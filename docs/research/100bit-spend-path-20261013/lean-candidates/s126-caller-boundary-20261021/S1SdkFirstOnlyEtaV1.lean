import S1SdkFirstOnlyPhysicalV1
import S1ReachedFinalEtaNumericV1
import S6SdkProofBufferV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisS1SdkFirstOnlyEta
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_NativeConsolidation
/-- SAME original accepted SDK witness, with the actual physical proof-account
bytes and extracted proof suffix, and full proof/public observations preserved
by the checkpoint write. No frame/alias/byte-identity assumption is added. -/
theorem original_sdk_physical_proof_eta {W A M Cv : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e : Entry) (world : W)
    (admission : S2W_D189Consolidation.RuntimeEntrypointAdmission L e world 3)
    (adapterOps : AdapterRw.Ops) (ops : Ops)

    (backend : AspisR1PublicPreparation.FinishModel.Boundaries)
    (native1 : S2W_ExtractionBoundary.First)
    (stage1 : AspisS6SdkFirstOnly.Stage1Extraction
      (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend))))
      native1)
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (initial final : A) (post : Heap (Nat → Record))
    (accepted : AspisS6SdkFirstObjectEquivalence.originalFirst native1 copy allocator e program data initial =
      ok (.Ok (out,post,final))) :
    post = writeBracket e.heap 2 0 0 (source (nativeBytes out)) ∧
    S2W_AccountObservations.observe S2W_ReturnedCheckpoint.encode e.metadata 3 post 1 =
      S2W_D189Interpretation.nativeObserve L S2W_ReturnedCheckpoint.encode e.metadata 3 world e.heap.ambient 1 ∧
    S2W_AccountObservations.observe S2W_ReturnedCheckpoint.encode e.metadata 3 post 0 =
      S2W_D189Interpretation.nativeObserve L S2W_ReturnedCheckpoint.encode e.metadata 3 world e.heap.ambient 0 ∧
    ∃ f : FirstCut,
      Slice.index_usize e.first 0#usize = ok f.proofAccount ∧
      Slice.index_usize e.first 1#usize = ok f.publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) f.proofAccount = ok (.Ok f.raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) f.publicAccount = ok (.Ok f.pub) ∧
      (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))).op47 f.pub = ok (.Ok f.statement) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.first_decoded (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) f.semantic f.pub f.proof f.split = ok (.Ok out) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        f.raw {start := 688#usize, «end» := 58295#usize} = ok f.proof ∧
      f.raw.val.length = 58295 ∧
      f.raw = e.buffers (e.handles 0).1 ∧
      payloadBytes S2W_ReturnedCheckpoint.encode (L.cellPayload world (L.accountData world 0))
        (L.cellPayload world (L.accountData world 0)).descriptor.length = MultiproofConeCanonical.bytesOf f.raw.val ∧
      (payloadBytes S2W_ReturnedCheckpoint.encode (L.cellPayload world (L.accountData world 0))
        (L.cellPayload world (L.accountData world 0)).descriptor.length).drop 688 = MultiproofConeCanonical.bytesOf f.proof.val ∧
      f.proof.val.length = 57607 ∧ f.raw.val = f.raw.val.take 688 ++ f.proof.val ∧
      f.pub = e.buffers (e.handles 1).1 ∧ f.pub.val.length = 1880 ∧
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
        (semanticBase ops (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend))).op9 (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend))) (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement))) v.semantic () none=ok (.Ok sem) ∧
        AspisR1PublicPreparation.PreparedScratchModel.prepare
          (concreteBoundaries (installedBoundaries (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed))
          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) ()
          (mapArray retainedE (Array.repeat 29#usize zero)) = ok (.Ok prepared,scratch) ∧
        powersPublic 29#usize prepared.gamma = ok scratch ∧
        AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize (toClaimE prepared.gamma) = ok (mapArray toClaimE scratch) ∧
        BorrowedClaimPrepared.claim (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) (retainedSem sem) v.y1
          (AspisR1SelectedWideViewV1.prepCarrier v.inactive) scratch prepared.kappa = ok (.Ok prepared.claim) ∧
        AspisS1SemanticArrayRanges.CurrentVerifiedNumeric sem ∧
        AspisS1SemanticArrayRanges.CurrentVerifiedChallengesNumeric sem ∧
        AspisS1ClaimAcceptedCallerRanges.CurrentClaimsNumeric sem ∧
        AspisS1MaskCallerDomains.MaskInputRanges (retainedSem sem) ∧
        AspisS1ReachedMaskInputs.ReachedMaskInputRanges
          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) (retainedSem sem) ∧
        AspisS1ReachedMaskCanonical.ReachedCanonicalMask
          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) (retainedSem sem) ∧
        AspisS1ReachedFinalNumeric.ReachedFinalNumeric backend
          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) (FirstComposition.toRetainedPublic (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic
              (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))) (retainedSem sem) ∧
        AspisS1ReachedFinalEtaNumeric.ReachedFinalEtaNumeric backend
          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) (FirstComposition.toRetainedPublic (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic
              (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))) (retainedSem sem) ∧
        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧
        OriginalPayloadClaimMeaning (retainedSem sem) v.y1
          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))
          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)
          (mapArray toClaimE scratch) ∧
        (∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
          Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
          Canonical value ∧ decode value=decode (toClaimE prepared.gamma)^i.val) ∧
        ExactSerializedRankTrace (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) p f.pub root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        Row31QueryProgramMeaning (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))) (AspisR1SelectedWideViewV1.preparedView v) prepared ∧
        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend))) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend))) f.pub f.proof f.split () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  obtain ⟨written,frame,proofFrame,f,ip,iu,rp,ru,dc,selection,called,ranged,rawLength,
    proofBuffer,observedProof,proofBytes,proofLength,shape,
    buffer,size,observed,nativeDecode,hk,zero,semantic,y1,view,sem,prepared,scratch,
    viewCall,variant,semanticCall,preparedCall,powers,early,claimed,numeric,challengeRanges,cells,
    maskDomains,reached,canonical,finalNumeric,seeds,claimMeaning,powerCells,trace,row31,tail⟩ :=
    AspisS1SdkFirstOnlyPhysical.original_sdk_physical_proof
      L sdk copy std allocator e world admission adapterOps ops backend native1 stage1
      p root length program data out initial final post accepted
  have finalEta := AspisS1ReachedFinalEtaNumeric.of_current backend _ _ sem finalNumeric challengeRanges
  exact ⟨written,frame,proofFrame,f,ip,iu,rp,ru,dc,selection,called,ranged,rawLength,
    proofBuffer,observedProof,proofBytes,proofLength,shape,
    buffer,size,observed,nativeDecode,hk,zero,semantic,y1,view,sem,prepared,scratch,
    viewCall,variant,semanticCall,preparedCall,powers,early,claimed,numeric,challengeRanges,cells,
    maskDomains,reached,canonical,finalNumeric,finalEta,seeds,claimMeaning,powerCells,trace,row31,tail⟩

#print axioms original_sdk_physical_proof_eta
end AspisS1SdkFirstOnlyEta
end
