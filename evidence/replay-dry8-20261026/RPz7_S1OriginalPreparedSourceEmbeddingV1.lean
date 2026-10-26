import RPz7_S1QueryTraceEmbeddingV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1CurrentCaller.OriginalPreparedInstallation
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete
open AspisR1PreparedSourcePowersBoundariesV1 AspisR1PreparedSourcePowersJointRankV1

/-- The enclosing first/Prepared.new result now installs the TOTAL actual
CodeField::from_m31 query-trace child. No free embedding callback or embedding
success/canonicality hypothesis remains. This is a concrete child installation,
not a claim that the other source children or SDK caller are closed. -/
theorem first_with_source_trace_embedding {E M Cv : Type} {L : Nat}
    (invalidAccountData : E) (ops : Ops)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : aspis_core.digest.Digest32 Unit) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : Array U8 32#usize) (length : U32)
    (error : verifier.Error → Result E) (bytes proof : Slice U8) (k : Usize)
    (out : alloc.vec.Vec U8)
    (h : FirstComposition.firstCurrent invalidAccountData (installOriginal ops sampling AspisS1M31Embedding.Total.embed)
      D error bytes proof k=ok (.Ok out)) :
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
        (sem : r1_semantic.Verified Unit) (prepared : AspisR1PublicPreparation.verifier.Prepared)
        (scratch : Array PE 29#usize),
        AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok v) ∧
        ops.op9 D (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) v.semantic () none=ok (.Ok sem) ∧
        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧
        OriginalPayloadClaimMeaning (retainedSem sem) v.y1
          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))
          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)
          (mapArray toClaimE scratch) ∧
        JointRankTrace sampling AspisS1M31Embedding.Total.embed (retainedDigest D) p pubInput root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        Tx1Reachability.afterPrepare (installOriginal ops sampling AspisS1M31Embedding.Total.embed) D bytes proof k () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  exact first_original_new_claim_and_rank invalidAccountData ops sampling
    AspisS1M31Embedding.Total.embed D p pubInput root length error bytes proof k out h

#print axioms first_with_source_trace_embedding
end AspisR1CurrentCaller.OriginalPreparedInstallation
