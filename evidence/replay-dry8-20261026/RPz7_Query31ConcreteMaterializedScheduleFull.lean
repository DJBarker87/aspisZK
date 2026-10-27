import RPz7_Query31ConcreteMaterializedSchedule
import Query31ConcreteDriverTraceFacts
import RPz7_Query31MathematicalSchedule
import Query31ModelScanCall

open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
open AspisR1.QuerySampler AspisR1PublicPreparation
open AspisR1PublicPreparation.Query31SourceSchedule
set_option autoImplicit false
noncomputable section


namespace Query31ConcreteMaterializedScheduleFull
theorem successful_concrete_materialized_query_schedule_full
    {H M Cv : Type} {L : Nat}
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice Std.U8) (root : TranscriptStep.Bytes32) (length : Std.U32)
    (self after : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
    (scan0 : Query31ModelDriverChain.QueryScan)
    (hstart : Query31ExplicitListLoop.validState scan0)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (out : Array Std.U32 22#usize)
    (hsuccess : QueriesModel.queries
      (Query31ConcreteMaterializedSchedule.concreteBoundaries scan0 embed) D self row payload = .ok (.Ok out, after)) :
    ∃ absorbed blocks advances selected',
      ∃ pairs : List (DigestPair D absorbed.hash),
        ∃ evidence sf,
      transcript.Transcript.absorb D self row payload = .ok absorbed ∧
      materializedOutputs
        pairs blocks advances ∧
      pairs.length = 8 ∧
      pairs.map (fun pair => decodeState pair.state) =
        (List.range pairs.length).map
          (fun i => AspisR1.QuerySampler.state p
            (SourceDigestOracle.oracle D absorbed.hash
              pubInput root length)
            (decodeState absorbed.state) i) ∧
      after = {absorbed with state := selected'} ∧
      (∀ pair ∈ pairs,
        decodeState pair.squeeze.output =
          SourceDigestOracle.oracle D absorbed.hash pubInput root length
            (FS2.Duplex.squeezeA p
              (decodeState pair.state)) ∧
        decodeState pair.advance.output =
          SourceDigestOracle.oracle D absorbed.hash pubInput root length
            (FS2.Duplex.advanceA p
              (decodeState pair.state))) ∧
      Query31ModelDriverChain.Q22ScanChain
        Query31ConcreteWordsDriverChain.actualQueryWords blocks scan0 evidence sf ∧
      evidence.length ≤ 8 ∧ Query31ExplicitListLoop.validState sf ∧
      (∀ e ∈ evidence, e.words.val = (List.range 8).map
        (fun j => AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
          (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord e.bytes j))) ∧
      ∃ stopIndex, AspisR1Query31Transcript.DriverTrace
        (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
        blocks advances scan0 out selected' ∧
        sf.accepted_len = 22#usize ∧ sf.accepted = out ∧
        AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish sf =
          .ok (.Ok out) ∧
        Array.index_usize advances stopIndex = .ok selected' ∧ stopIndex.val ≤ 7 := by
  let B := Query31ConcreteMaterializedSchedule.concreteBoundaries scan0 embed
  obtain ⟨absorbed, blocks, advances, selected', pairs, habs, hdecode, hafter,
      hlen, hmaterial, hstates, hfunctional⟩ :=
    AspisR1PublicPreparation.Query31SourceSchedule.queries_success_on_querySampler_schedule
      B D p pubInput root length self after row payload out hsuccess
  have hdecoded : Query31ConcreteMaterializedSchedule.actualConcreteDecode scan0 blocks advances = .ok (.Ok (out, selected')) := hdecode
  unfold Query31ConcreteMaterializedSchedule.actualConcreteDecode at hdecoded
  have hscan : AspisR1Query31Transcript.queries_from_pairs_with_scan
      (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
      scan0 blocks advances = .ok (.Ok (out, selected')) :=
    Query31ConcreteMaterializedSchedule.adaptScanResult_success hdecoded
  let trace := AspisR1Query31Transcript.successful_driver_has_trace
    (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
    scan0 blocks advances out selected' hscan
  obtain ⟨evidence, sf, stopIndex, hchain, hlenEvidence, hvalidFinal,
      hfinish, hcount, hbuffer, hadvance, hindexBound⟩ :=
    Query31ConcreteDriverTraceFacts.driver_trace_q22_chain_with_finish
      Query31ConcreteWordsDriverChain.actualQueryWords blocks advances scan0 out selected'
      hstart trace
  have hwords := Query31ConcreteWordsDriverChain.chain_words_are_concrete
    blocks scan0 sf evidence hchain
  have hcount22 : sf.accepted_len = 22#usize := by
    simpa [AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT] using hcount
  refine ⟨absorbed, blocks, advances, selected', pairs, evidence, sf,
    habs, hmaterial, hlen, hstates, hafter, hfunctional,
    hchain, hlenEvidence, hvalidFinal, hwords,
    stopIndex, trace, hcount22, hbuffer, hfinish, hadvance, hindexBound⟩


theorem successful_default_concrete_materialized_query_schedule
    {H M Cv : Type} {L : Nat}
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice Std.U8) (root : TranscriptStep.Bytes32) (length : Std.U32)
    (self after : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (out : Array Std.U32 22#usize)
    (hsuccess : QueriesModel.queries
      (Query31ConcreteMaterializedSchedule.concreteBoundaries
        Query31ConcreteDriverTraceFacts.sourceDefaultState embed)
      D self row payload = .ok (.Ok out, after)) :
    ∃ absorbed blocks advances selected',
      ∃ pairs : List (DigestPair D absorbed.hash),
        ∃ evidence sf,
      transcript.Transcript.absorb D self row payload = .ok absorbed ∧
      materializedOutputs pairs blocks advances ∧ pairs.length = 8 ∧
      pairs.map (fun pair => decodeState pair.state) =
        (List.range pairs.length).map
          (fun i => AspisR1.QuerySampler.state p
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
        Query31ConcreteWordsDriverChain.actualQueryWords blocks
        Query31ConcreteDriverTraceFacts.sourceDefaultState evidence sf ∧
      evidence.length ≤ 8 ∧ Query31ExplicitListLoop.validState sf ∧
      (∀ e ∈ evidence, e.words.val = (List.range 8).map
        (fun j => AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
          (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord e.bytes j))) ∧
      ∃ stopIndex,
        AspisR1Query31Transcript.DriverTrace
          (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
          blocks advances Query31ConcreteDriverTraceFacts.sourceDefaultState out selected' ∧
        sf.accepted_len = 22#usize ∧ sf.accepted = out ∧
        AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish sf =
          .ok (.Ok out) ∧
        Array.index_usize advances stopIndex = .ok selected' ∧ stopIndex.val ≤ 7 := by
  obtain ⟨absorbed, blocks, advances, selected', pairs, evidence, sf,
      habs, hmaterial, hlen, hstates, hafter, hfunctional,
      hchain, hlenEvidence, hvalidFinal, hwords,
      stopIndex, trace, hcount22, hbuffer, hfinish, hadvance, hindexBound⟩ :=
    successful_concrete_materialized_query_schedule_full
    D p pubInput root length self after row payload
    Query31ConcreteDriverTraceFacts.sourceDefaultState
    Query31ConcreteDriverTraceFacts.sourceDefaultState_valid embed out hsuccess
  exact ⟨absorbed, blocks, advances, selected', pairs, evidence, sf,
    habs, hmaterial, hlen, hstates, hafter, hfunctional,
    hchain, hlenEvidence, hvalidFinal, hwords,
    stopIndex, trace, hcount22, hbuffer, hfinish, hadvance, hindexBound⟩

#print axioms successful_concrete_materialized_query_schedule_full
#print axioms successful_default_concrete_materialized_query_schedule

end Query31ConcreteMaterializedScheduleFull
end
