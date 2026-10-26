import RPz7_S1BorrowedClaimConcreteCallerV1
import RPz7_S1OwnedStage1NumericV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisS1NativeBufferClaimTrace
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation

/-- Exact pre-prepare dictionary of the already installed native-buffer caller.
No callee, record, result, observer or semantic value is replaced. -/
def semanticBase (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries) : Ops :=
  S1SemanticInstallation.install
    {(withValues ops) with op10 := AspisS1NativeCompact.compact.expand_semantic nativeValues}
    AspisS1ExtractedRoundChildren.children B

theorem install_exact (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B =
      BorrowedClaimPrepared.install (semanticBase ops B) (withOriginalSerializer closedSampling)
        AspisS1M31Embedding.Total.embed := rfl

/-- The same accepted first on the concrete current expansion/round/preparation
installation yields the source claim meaning, SAME reused gamma scratch and
joint serialized challenge trace. Semantic numeric ranges are derived from
that same child return. Root/length/p remain trace-interpretation parameters. -/
theorem first_native_buffers_claim_trace {E M Cv : Type} {L : Nat}
    (invalidAccountData : E) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (D : aspis_core.digest.Digest32 Unit) (p : FS2.Duplex.Params M Cv L)
    (root : Array U8 32#usize) (length : U32)
    (error : verifier.Error → Result E) (bytes proof : Slice U8) (k : Usize)
    (out : alloc.vec.Vec U8)
    (h : FirstComposition.firstCurrent invalidAccountData (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      D error bytes proof k=ok (.Ok out)) :
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
        (sem : r1_semantic.Verified Unit) (prepared : AspisR1PublicPreparation.verifier.Prepared)
        (scratch : Array PE 29#usize),
        AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok v) ∧
        (semanticBase ops B).op9 D (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) v.semantic () none=ok (.Ok sem) ∧
        AspisS1SemanticArrayRanges.CurrentVerifiedNumeric sem ∧
        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧
        OriginalPayloadClaimMeaning (retainedSem sem) v.y1
          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))
          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)
          (mapArray toClaimE scratch) ∧
        (∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
          Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
          Canonical value ∧ decode value=decode (toClaimE prepared.gamma)^i.val) ∧
        ExactSerializedRankTrace (retainedDigest D) p bytes root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) D bytes proof k () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  have hc := first_concrete_borrowed_reference invalidAccountData (semanticBase ops B)
    closedSampling D p bytes root length error bytes proof k out h
  obtain ⟨statement,decoded,split,zero,semantic,y1,view,sem,prepared,scratch,
    viewCall,semanticCall,seeds,claim,powers,trace,tail⟩ := hc
  have verify : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children B
      D (FirstComposition.toCurrentPublic
        (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
      view.semantic () = ok (.Ok sem) := semanticCall
  have numeric := AspisS1SemanticArrayRanges.installed_verify_numeric B D _ view.semantic () sem verify
  exact ⟨statement,decoded,split,zero,semantic,y1,view,sem,prepared,scratch,
    viewCall,semanticCall,numeric,seeds,claim,powers,trace,tail⟩

#print axioms install_exact
#print axioms first_native_buffers_claim_trace
end AspisS1NativeBufferClaimTrace
end
