import S1AcceptedChallengesNumericV1
import S1NativeBufferPreparedTraceV1
import SInt2_S6SdkOriginalObjectCallerV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisS1SdkPreparedChallengeRanges
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_NativeConsolidation
/-- ONE original SDK wrapper acceptance supplies actual Prepared.new, the same
reused gamma scratch and borrowed claim, joint challenge trace and the actual
S2 row31/32 program on EVERY matching enclosing caller cut. All source/runtime/
Std/extraction boundaries remain the named standing ones. -/
theorem original_sdk_prepared_claim_trace_ranges {W A M Cv : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e : Entry) (world : W)
    (admission : S2W_D189Consolidation.RuntimeEntrypointAdmission L e world 3)
    (adapterOps : AdapterRw.Ops) (ops : Ops)

    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
      native1 native2 hashv)
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (initial final : A) (post : Heap (Nat → Record))
    (accepted : AspisS6SdkFirstObjectEquivalence.originalFirst native1 copy allocator e program data initial =
      ok (.Ok (out,post,final))) :
    post = writeBracket e.heap 2 0 0 (source (nativeBytes out)) ∧
    S2W_AccountObservations.observe S2W_ReturnedCheckpoint.encode e.metadata 3 post 1 =
      S2W_D189Interpretation.nativeObserve L S2W_ReturnedCheckpoint.encode e.metadata 3 world e.heap.ambient 1 ∧
    ∀ (accounts2 : Slice AdapterRw.Cuts.Account) (f : FirstCut) (s : SecondCut),
      SourceCuts (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
        e.first accounts2 out f s →
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
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  obtain ⟨written,frame,allCuts⟩ := AspisS6SdkOriginalObjectCaller.original_sdk_all_cuts
    L sdk copy std allocator e world admission adapterOps
    (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
    native1 native2 hashv extraction program data initial final out post accepted
  refine ⟨written,frame,?_⟩
  intro accounts2 f s cuts
  obtain ⟨buffer,size,observed,encoded,decoded,nativeDecode,encodedCall,encodedBytes,split,first⟩ :=
    allCuts accounts2 f s cuts
  obtain ⟨statement,hd,hk,zero,semantic,y1,view,sem,prepared,scratch,
    viewCall,variant,semanticCall,preparedCall,powers,early,claimed,numeric,
    seeds,claimMeaning,powerCells,trace,row31,tail⟩ :=
    first_native_buffers_prepared_trace AdapterRw.solana_program_error.ProgramError.InvalidAccountData
      ops B (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      p root length (fun error => adapterOps.op44 (AspisS6CurrentVerifierCarrier.fromError error))
      f.pub f.proof f.split out first
  have sameStatement := core.result.Result.Ok.inj (Result.ok.inj (hd.symm.trans nativeDecode))
  subst statement
  have challengeRanges := AspisS1SemanticArrayRanges.installed_verify_challenges B
    (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
    (FirstComposition.toCurrentPublic
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic
        (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))
    view.semantic () sem semanticCall
  exact ⟨buffer,size,observed,nativeDecode,hk,zero,semantic,y1,view,sem,prepared,scratch,
    viewCall,variant,semanticCall,preparedCall,powers,early,claimed,numeric,challengeRanges,
    seeds,claimMeaning,powerCells,trace,row31,tail⟩

#print axioms original_sdk_prepared_claim_trace_ranges
end AspisS1SdkPreparedChallengeRanges
end
