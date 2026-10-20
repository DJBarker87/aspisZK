import Query31ConcreteWordsDriverChain
import Query31MathematicalSchedule
import Query31ModelScanCall

open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
open AspisR1.QuerySampler AspisR1PublicPreparation
open AspisR1PublicPreparation.Query31SourceSchedule
set_option autoImplicit false
noncomputable section

namespace Query31ConcreteMaterializedSchedule

abbrev SourceQueryError :=
  AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError
abbrev ScheduleQueryError :=
  AspisR1PublicPreparation.aspis_core.transcript.QuerySampleError
abbrev QueryOutput := (Array Std.U32 22#usize) × (Array Std.U8 32#usize)

/-- Constructor-preserving conversion between the private scan model's error
    type and the current extracted schedule model's nominal error type. -/
def adaptQueryError : SourceQueryError → ScheduleQueryError
  | .BoundNotPowerOfTwo b => .BoundNotPowerOfTwo b
  | .CountExceedsBound n b => .CountExceedsBound n b
  | .DrawLimitExhausted n m => .DrawLimitExhausted n m

/-- Lift the checked local first-stop driver into the generated query-model
    error type without changing its successful output or continuation. -/
def adaptScanResult
    (r : Result (core.result.Result QueryOutput SourceQueryError)) :
    Result (core.result.Result QueryOutput ScheduleQueryError) :=
  match r with
  | .ok (.Ok out) => .ok (.Ok out)
  | .ok (.Err e) => .ok (.Err (adaptQueryError e))
  | .fail e => .fail e
  | .div => .div

def actualConcreteDecode (scan0 : Query31ModelDriverChain.QueryScan)
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize) :
    Result (core.result.Result QueryOutput ScheduleQueryError) :=
  adaptScanResult <| AspisR1Query31Transcript.queries_from_pairs_with_scan
    (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
    scan0 blocks advances

def concreteBoundaries (scan0 : Query31ModelDriverChain.QueryScan)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact) :
    AspisR1PublicPreparation.QueriesModel.Boundaries :=
  { decode := actualConcreteDecode scan0, embed := embed }

theorem adaptScanResult_success {out : QueryOutput} {r :
    Result (core.result.Result QueryOutput SourceQueryError)}
    (h : adaptScanResult r = .ok (.Ok out)) : r = .ok (.Ok out) := by
  cases r with
  | ok inner =>
      cases inner with
      | Ok a =>
          simp [adaptScanResult] at h
          change a = out at h
          subst out
          rfl
      | Err e => simp [adaptScanResult] at h
  | fail e => simp [adaptScanResult] at h
  | div => simp [adaptScanResult] at h

/-- A successful concrete Q22 scan through the actual source `query_words`
    decoder, when run over the eight digest blocks materialized by the actual
    extracted query schedule, is tied to the retained `QuerySampler` state
    recurrence. The materialized arrays and the scan chain share the same
    `blocks`/`advances`; the query word theorem fixes the byte order and mask.

    The exact production caller lowering from `queries_from_pairs` to this
    first-stop model, and the Rust standard-library iterator implementation,
    remain separate correspondence boundaries. -/
theorem successful_concrete_materialized_query_schedule
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
      (concreteBoundaries scan0 embed) D self row payload = .ok (.Ok out, after)) :
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
      ∀ e ∈ evidence, e.words.val = (List.range 8).map
        (fun j => AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord
          (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord e.bytes j)) := by
  let B := concreteBoundaries scan0 embed
  obtain ⟨absorbed, blocks, advances, selected', pairs, habs, hdecode, hafter,
      hlen, hmaterial, hstates, hfunctional⟩ :=
    AspisR1PublicPreparation.Query31SourceSchedule.queries_success_on_querySampler_schedule
      B D p pubInput root length self after row payload out hsuccess
  have hdecoded : actualConcreteDecode scan0 blocks advances = .ok (.Ok (out, selected')) := hdecode
  unfold actualConcreteDecode at hdecoded
  have hscan : AspisR1Query31Transcript.queries_from_pairs_with_scan
      (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
      scan0 blocks advances = .ok (.Ok (out, selected')) :=
    adaptScanResult_success hdecoded
  obtain ⟨evidence, sf, hchain, hlenEvidence, hvalidFinal, hwords⟩ :=
    Query31ConcreteWordsDriverChain.successful_driver_has_concrete_q22_chain
      blocks advances scan0 out selected' hstart hscan
  refine ⟨absorbed, blocks, advances, selected', pairs, evidence, sf, habs, hmaterial,
    hlen, hstates, hafter, hfunctional, hchain, hlenEvidence, hvalidFinal, hwords⟩

#print axioms adaptScanResult_success
#print axioms successful_concrete_materialized_query_schedule

end Query31ConcreteMaterializedSchedule
end
