import CurrentPreparedJointRankPrefix
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
open AspisR1.QuerySampler AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1Query31Transcript AspisV8R19.Q22WordScan
open Query31ModelDriverChain Query31ExplicitListLoop Query31ModelScanCall
open Query31ConcreteMaterializedSchedule Query31ConcreteDriverTraceFacts
open Query31ConcreteMaterializedScheduleFull
namespace AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1PublicPreparation
open AspisR1Post25SamplerOrdinaryRankV1
open PreparedFromQmSourceBridge CurrentQueryRho
local notation "Wide" => aspis_core.field.WideExact
local notation "ordinaryBoundary" => AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary

def ConcreteQueryRhoFacts {H M Cv : Type} {L : Nat}
    (embed : aspis_core.field.M31 → Result Wide)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (v : verifier.View) (out : verifier.Prepared) (row : U8) (before : transcript.Transcript H) : Prop :=
  ∃ (afterQueries last : transcript.Transcript H) (block : Array U8 32#usize),
    QueriesModel.queries (Query31ConcreteMaterializedSchedule.concreteBoundaries sourceDefaultState embed)
      D before row v.final_message=ok (.Ok out.queries,afterQueries) ∧
    QueryScheduleFacts D p pubInput root length before afterQueries row v.final_message out.queries ∧
    transcript.Transcript.block D afterQueries (if row=30#u8 then 31#u8 else 32#u8)
      PreparedScratchReachability.emptyPayload=ok (block,last) ∧
    sampler.qm31_sample block=ok out.rho ∧
    AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld out.rho)) ∧
    AspisR1.ExtractedQM31SamplerCorrect.coordinates (SamplerTransport.toOld out.rho)=
      AspisR1.SamplerNatModel.qm31Digits (AspisR1.SourceSamplerByteRank.rank block) ∧
    out.state=last.state

theorem afterQueries_concrete_query_rho {H M Cv : Type} {L : Nat}
    (sampling : PreparedModel.Boundaries) (embed : aspis_core.field.M31 → Result Wide)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (gamma kappa : Wide)
    (alpha : Array Wide 2#usize) (row : U8) (before : transcript.Transcript H)
    (out : verifier.Prepared) (scratch : Array Wide 29#usize)
    (h : PreparedScratchReachability.AfterQueries
      (AspisR1ClaimPreparedBridge.concreteBoundaries (installedBoundaries sampling embed))
      D sem v gamma kappa alpha row before out scratch) :
    ConcreteQueryRhoFacts embed D p pubInput root length v out row before := by
  obtain ⟨afterQueries,last,block,hq,hblock,hsample,hcan,hcoords,hstate⟩ :=
    CurrentRho.afterQueries_rho_meaning
      (AspisR1ClaimPreparedBridge.concreteBoundaries (installedBoundaries sampling embed))
      D sem v gamma kappa alpha row before out scratch h
  change QueriesModel.queries (Query31ConcreteMaterializedSchedule.concreteBoundaries sourceDefaultState embed)
    D before row v.final_message=ok (.Ok out.queries,afterQueries) at hq
  have hs := successful_default_concrete_materialized_query_schedule
    D p pubInput root length before afterQueries row v.final_message embed out.queries hq
  exact ⟨afterQueries,last,block,hq,hs,hblock,hsample,hcan,hcoords,hstate⟩

def RankedTailFacts {H M Cv : Type} {L : Nat}
    (embed : aspis_core.field.M31 → Result Wide)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (v : verifier.View) (out : verifier.Prepared) (alpha0 : Wide)
    (before : transcript.Transcript H) : Prop :=
  (transport.Variant.folds v.variant=ok 1#usize ∧
    out.alpha=Array.make 2#usize [alpha0,aspis_core.field.WideExact.ZERO] ∧
    ConcreteQueryRhoFacts embed D p pubInput root length v out 30#u8 before) ∨
  ∃ (foldedRoot : Array U8 32#usize) (bytes1 bytes2 : alloc.vec.Vec U8)
    (alpha1 : Wide) (afterAlpha : transcript.Transcript H) (block : Array U8 32#usize),
    transport.Variant.folds v.variant=ok 2#usize ∧
    core.option.Option.unwrap v.folded_root=ok foldedRoot ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8
      (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice foldedRoot)=ok bytes1 ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 v.round1=ok bytes2 ∧
    transcript.Transcript.block D before 30#u8 (alloc.vec.Vec.deref bytes2)=ok (block,afterAlpha) ∧
    OrdinaryRankMeaning block alpha1 ∧
    out.alpha=Array.make 2#usize [alpha0,alpha1] ∧
    ConcreteQueryRhoFacts embed D p pubInput root length v out 31#u8 afterAlpha

theorem tail_ranked_facts {H M Cv : Type} {L : Nat}
    (sampling : PreparedModel.Boundaries) (embed : aspis_core.field.M31 → Result Wide)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (gamma kappa alpha0 : Wide)
    (before : transcript.Transcript H) (out : verifier.Prepared) (scratch : Array Wide 29#usize)
    (h : PreparedScratchReachability.Tail
      (AspisR1ClaimPreparedBridge.concreteBoundaries (installedBoundaries sampling embed))
      D sem v gamma kappa alpha0 before out scratch) :
    RankedTailFacts embed D p pubInput root length v out alpha0 before := by
  cases h with
  | single hf ha =>
    have halpha : out.alpha=Array.make 2#usize [alpha0,aspis_core.field.WideExact.ZERO] := by
      obtain ⟨queries,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := ha
      subst out
      rfl
    exact Or.inl ⟨hf,halpha,afterQueries_concrete_query_rho sampling embed D p pubInput root length
      sem v gamma kappa _ _ _ out scratch ha⟩
  | double hf foldedRoot bytes1 bytes2 alpha1 afterAlpha hroot hb1 hb2 ha1 ha =>
    let base := withSourceFromQm (CurrentQueryRho.withConcreteQueries sampling embed)
    change PreparedModel.scalar (ordinaryBoundary (withCandidateGamma base))
      D before 30#u8 (alloc.vec.Vec.deref bytes2) false=ok (alpha1,afterAlpha) at ha1
    obtain ⟨block,hblock,hrank⟩ := scalar_candidate_ordinary_rank (withCandidateGamma base)
      D before afterAlpha 30#u8 (alloc.vec.Vec.deref bytes2) alpha1 ha1
    have halpha : out.alpha=Array.make 2#usize [alpha0,alpha1] := by
      obtain ⟨queries,afterQueries,last,rho,claim,hq,hr,hp,hc,he⟩ := ha
      subst out
      rfl
    exact Or.inr ⟨foldedRoot,bytes1,bytes2,alpha1,afterAlpha,block,hf,hroot,hb1,hb2,hblock,hrank,
      halpha,afterQueries_concrete_query_rho sampling embed D p pubInput root length
        sem v gamma kappa _ _ _ out scratch ha⟩

#print axioms afterQueries_concrete_query_rho
#print axioms tail_ranked_facts
end AspisR1ClaimPreparedBridge.InstalledMeaning
