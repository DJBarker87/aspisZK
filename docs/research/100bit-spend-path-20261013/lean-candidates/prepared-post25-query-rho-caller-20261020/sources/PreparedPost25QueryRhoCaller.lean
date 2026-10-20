import ExtractedOpeningRun
import ExtractedOpeningCalls
import ExtractedDigest32SamplerTransport
import Query31ConcreteMaterializedScheduleFull

set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
open AspisR1.QuerySampler AspisR1PublicPreparation
open AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1Query31Transcript AspisV8R19.Q22WordScan
open Query31ModelDriverChain Query31ExplicitListLoop Query31ModelScanCall

namespace AspisR1PublicPreparation.Post25QueryRhoCaller

open AspisR1PublicPreparation.OpeningRun
open AspisR1PublicPreparation.PreparedReachability
open AspisR1PublicPreparation.SamplerTransport
open Query31ConcreteMaterializedSchedule
open Query31ConcreteDriverTraceFacts
open Query31ConcreteMaterializedScheduleFull

/-- All output-bearing facts from the concrete row-31 query model. -/
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

/-- A successful two-fold preparation with the concrete row-31 query boundary
runs the same default-state first-stop/materialization model and then samples
rho from row 32 of the transcript returned by that very query. -/
theorem prepare_success_concrete_query_rho
    {H M Cv : Type} {L : Nat}
    (B : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice Std.U8) (root : TranscriptStep.Bytes32) (length : Std.U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (out : verifier.Prepared)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (hfolds : transport.Variant.folds v.variant = .ok 2#usize)
    (hprep : PreparedModel.prepare
      (OpeningRun.bindQueries B (Query31ConcreteMaterializedSchedule.concreteBoundaries
        Query31ConcreteDriverTraceFacts.sourceDefaultState embed))
      D sem v hash = .ok (.Ok out)) :
    ∃ before : transcript.Transcript H,
      ∃ queries : Array U32 22#usize,
      ∃ afterQueries last : transcript.Transcript H,
        ∃ block : Array U8 32#usize,
          QueriesModel.queries
            (Query31ConcreteMaterializedSchedule.concreteBoundaries sourceDefaultState embed)
            D before 31#u8 v.final_message = .ok (.Ok queries, afterQueries) ∧
          out.queries = queries ∧
          QueryScheduleFacts D p pubInput root length before afterQueries
            31#u8 v.final_message queries ∧
          transcript.Transcript.block D afterQueries 32#u8 emptyPayload = .ok (block, last) ∧
          sampler.qm31_sample block = .ok out.rho ∧
          AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
            (AspisR1.ExtractedQM31SamplerCarrier.toCurrent (toOld out.rho)) ∧
          AspisR1.ExtractedQM31SamplerCorrect.coordinates (toOld out.rho) =
            AspisR1.SamplerNatModel.qm31Digits (AspisR1.SourceSamplerByteRank.rank block) := by
  have hr := PreparedReachability.prepare_success
    (OpeningRun.bindQueries B (Query31ConcreteMaterializedSchedule.concreteBoundaries
      sourceDefaultState embed)) D sem v hash out hprep
  rcases hr with ⟨start,t1,t2,t3,inactiveBytes,gamma,kappa,alpha0,
    hseed,hgamma,hbytes,hkappa,halpha0,htail⟩
  cases htail with
  | single hf tail =>
      simp [hfolds] at hf
  | double hf foldRoot bytes1 bytes2 alpha1 afterAlpha hroot hbytes1 hbytes2 halpha1 tail =>
      rcases tail with ⟨queries, afterQueries, last, rho, claim,
        hqueries, hrho, hclaim, hout⟩
      have hqueriesConcrete : QueriesModel.queries
          (Query31ConcreteMaterializedSchedule.concreteBoundaries sourceDefaultState embed)
          D afterAlpha 31#u8 v.final_message =
          .ok (.Ok queries, afterQueries) := by
        simpa [OpeningRun.bindQueries] using hqueries
      have hbefore : out.queries = queries := by
        have hp := congrArg (fun p : verifier.Prepared => p.queries) hout
        simpa [PreparedReachability.output] using hp
      have hschedule :=
        successful_default_concrete_materialized_query_schedule
          D p pubInput root length afterAlpha afterQueries 31#u8 v.final_message
          embed queries hqueriesConcrete
      have houtRho : out.rho = rho := by
        have hp := congrArg (fun p : verifier.Prepared => p.rho) hout
        simpa [PreparedReachability.output] using hp
      obtain ⟨block,hblock,hsample⟩ :=
        AspisR1PublicPreparation.OpeningCalls.rho_success
          (OpeningRun.bindQueries B
            (Query31ConcreteMaterializedSchedule.concreteBoundaries sourceDefaultState embed))
          D afterQueries last 32#u8 PreparedReachability.emptyPayload rho hrho
      have hsampleOut : sampler.qm31_sample block = .ok out.rho := by
        simpa [houtRho] using hsample
      obtain ⟨q0,hq0,hcanonical,hcoords⟩ := SamplerTransport.sample_total block
      have heq : out.rho = q0 := Result.ok.inj (hsampleOut.symm.trans hq0)
      have hcanonOut :
          AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
            (AspisR1.ExtractedQM31SamplerCarrier.toCurrent (toOld out.rho)) := by
        simpa [heq] using hcanonical
      have hcoordsOut :
          AspisR1.ExtractedQM31SamplerCorrect.coordinates (toOld out.rho) =
            AspisR1.SamplerNatModel.qm31Digits (AspisR1.SourceSamplerByteRank.rank block) := by
        simpa [heq] using hcoords
      refine ⟨afterAlpha, queries, afterQueries, last, block,
        hqueriesConcrete, hbefore, hschedule, hblock, hsampleOut, hcanonOut, hcoordsOut⟩

#print axioms prepare_success_concrete_query_rho

end AspisR1PublicPreparation.Post25QueryRhoCaller
