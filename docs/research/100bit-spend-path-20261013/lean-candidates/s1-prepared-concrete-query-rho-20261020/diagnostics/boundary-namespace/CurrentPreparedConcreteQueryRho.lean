import CurrentPreparedRhoMeaning
import Query31ConcreteMaterializedScheduleFull
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
open AspisR1.QuerySampler AspisR1PublicPreparation
open AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1Query31Transcript AspisV8R19.Q22WordScan
open Query31ModelDriverChain Query31ExplicitListLoop Query31ModelScanCall
namespace AspisR1ClaimPreparedBridge.CurrentQueryRho
open Query31ConcreteMaterializedSchedule
open Query31ConcreteDriverTraceFacts
open Query31ConcreteMaterializedScheduleFull

def QueryScheduleFacts
    {H M Cv : Type} {L : Nat}
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice Std.U8) (root : TranscriptStep.Bytes32) (length : Std.U32)
    (self after : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
    (out : Array Std.U32 22#usize) : Prop :=
  ∃ absorbed blocks advances selected',
    ∃ pairs : List (DigestPair D absorbed.hash),
      ∃ evidence sf,
      transcript.Transcript.absorb D self row payload = .ok absorbed ∧
      materializedOutputs pairs blocks advances ∧
      pairs.length = 8 ∧
      pairs.map (fun pair => decodeState pair.state) =
        (List.range pairs.length).map (fun i => AspisR1.QuerySampler.state p
          (SourceDigestOracle.oracle D absorbed.hash pubInput root length)
          (decodeState absorbed.state) i) ∧
      after = {absorbed with state := selected'} ∧
      (∀ pair ∈ pairs,
        decodeState pair.squeeze.output =
          SourceDigestOracle.oracle D absorbed.hash pubInput root length
            (FS2.Duplex.squeezeA p (decodeState pair.state)) ∧
        decodeState pair.advance.output =
          SourceDigestOracle.oracle D absorbed.hash pubInput root length
            (FS2.Duplex.advanceA p (decodeState pair.state))) ∧
      Query31ModelDriverChain.Q22ScanChain
        Query31ConcreteWordsDriverChain.actualQueryWords blocks sourceDefaultState evidence sf ∧
      evidence.length ≤ 8 ∧ Query31ExplicitListLoop.validState sf ∧
      (∀ e ∈ evidence, e.words.val = (List.range 8).map
        (fun j => AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
          (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord e.bytes j))) ∧
      ∃ stopIndex,
        AspisR1Query31Transcript.DriverTrace
          (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
          blocks advances sourceDefaultState out selected' ∧
        sf.accepted_len = 22#usize ∧ sf.accepted = out ∧
        AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish sf =
          .ok (.Ok out) ∧
        Array.index_usize advances stopIndex = .ok selected' ∧ stopIndex.val ≤ 7


def withConcreteQueries (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact) : PreparedModel.Boundaries :=
  {sampling with queries:=fun D self row payload =>
    QueriesModel.queries (concreteBoundaries sourceDefaultState embed) D self row payload}

theorem prepared_success_concrete_query_rho {H M Cv : Type} {L : Nat}
    (sampling : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (out : verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : PreparedScratchModel.prepare
      (AspisR1ClaimPreparedBridge.concreteBoundaries (withConcreteQueries sampling embed))
      D sem v hash scratchIn=ok (.Ok out,scratch)) :
    ∃ (row : U8) (before afterQueries last : transcript.Transcript H) (block : Array U8 32#usize),
      (row=30#u8 ∨ row=31#u8) ∧
      QueriesModel.queries (concreteBoundaries sourceDefaultState embed)
        D before row v.final_message=ok (.Ok out.queries,afterQueries) ∧
      QueryScheduleFacts D p pubInput root length before afterQueries row v.final_message out.queries ∧
      transcript.Transcript.block D afterQueries (if row=30#u8 then 31#u8 else 32#u8)
        PreparedScratchReachability.emptyPayload=ok (block,last) ∧
      sampler.qm31_sample block=ok out.rho ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld out.rho)) ∧
      AspisR1.ExtractedQM31SamplerCorrect.coordinates (SamplerTransport.toOld out.rho)=
        AspisR1.SamplerNatModel.qm31Digits (AspisR1.SourceSamplerByteRank.rank block) ∧
      out.state=last.state := by
  obtain ⟨row,before,hrow,hfacts⟩ := CurrentRho.prepared_success_rho_meaning
    (AspisR1ClaimPreparedBridge.concreteBoundaries (withConcreteQueries sampling embed))
    D sem v hash out scratch scratchIn h
  obtain ⟨afterQueries,last,block,hq,hblock,hsample,hcan,hcoords,hstate⟩ := hfacts
  change QueriesModel.queries (concreteBoundaries sourceDefaultState embed)
    D before row v.final_message=ok (.Ok out.queries,afterQueries) at hq
  have hs := successful_default_concrete_materialized_query_schedule
    D p pubInput root length before afterQueries row v.final_message embed out.queries hq
  exact ⟨row,before,afterQueries,last,block,hrow,hq,hs,hblock,hsample,hcan,hcoords,hstate⟩

#print axioms prepared_success_concrete_query_rho
end AspisR1ClaimPreparedBridge.CurrentQueryRho
