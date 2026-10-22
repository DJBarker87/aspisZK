import Query31SourceOracleBridge
import R4Transport2QueryAbsorb
import Query31MathematicalSchedule
import Query31ConcreteMaterializedSchedule
import Query31ConcreteDriverTraceFacts
import Query31ConcreteWordsDriverChain
import Query31ModelScanCall
import Query31ExplicitScanBody
import Query31ExplicitListLoop
import Query31DriverTraceScanOutV1
import S4LiteralRow31PairsJoinV1
import S4SourcePairsToFunctionsV1
import S4Row31SourceTraceConsumerV1
import S4QueryArrayOrderV1
import S4SolanaDigestWrapperP3BindingV1
import S4P3SourceInterpretationV1

open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation
open AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1PublicPreparation.SourceDigestOracle
open AspisR1PublicPreparation.R4Transport2OpeningChain
open AspisR1PublicPreparation.R4Transport2QueryPrefix
open AspisR1PublicPreparation.TranscriptStep
open AspisR1.QuerySampler AspisR1.QueryStateList AspisR1.TranscriptView
open S4SolanaDigestWrapperP3BindingV1
open AspisR1.S4P3SourceInterpretationV1
set_option autoImplicit false
noncomputable section

namespace AspisR1.S4ChosenModelRow31AcceptanceV1

theorem successful_queries_row31_literal_acceptance
    {M Cv : Type} {L : Nat}
    (sha256 : Bytes → Array U8 32#usize)
    (p : Params M Cv L) (pubInput : Slice U8) (root : Bytes32) (length : U32)
    (self after : transcript.Transcript SolanaDigest) (payload : Slice U8)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (out : Array U32 22#usize)
    (hquery : QueriesModel.queries
      (Query31ConcreteMaterializedSchedule.concreteBoundaries
        Query31ConcreteDriverTraceFacts.sourceDefaultState embed)
      (p3PublicDigest32 sha256) self 31#u8 payload = .ok (.Ok out, after))
    (fits : (R4Transport2OpeningChain.framed payload).length ≤ SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state) :
    (AspisV8R19.MemoizedProgramLaw.eval (fun bs => hashBytes sha256 bs)
      (AspisR1.LiteralByteSampler.samp 31 P
        (.payload (R4Transport2OpeningChain.message payload fits))).toProgram).2 =
      (Value.queries (.ok (out.val.map (fun w => w.val))), decodeState after.state) ∧
    ∃ q, LiteralQueryRead.decode (out.val.map (fun w => w.val)) = some q ∧
      ∀ j : Fin 22, (out.val[j.val]'(by scalar_tac)).val = (q j).val := by
  let B := Query31ConcreteMaterializedSchedule.concreteBoundaries
    Query31ConcreteDriverTraceFacts.sourceDefaultState embed
  obtain ⟨absorbed, blocks, advances, selected, sourcePairs,
      habs, hdecode, hafter, hlen, hfirst, hchain, hfunctional, hmaterial⟩ :=
    AspisR1PublicPreparation.Query31SourceSchedule.queries_success_pairs_functional_full
      B (p3PublicDigest32 sha256) p pubInput root length self after 31#u8 payload out hquery
  have hdecoded : Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances =
        .ok (.Ok (out, selected)) := by
    change Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances = _
    exact hdecode
  have hscan := Query31ConcreteMaterializedSchedule.adaptScanResult_success hdecoded
  have hdriverTrace := AspisR1Query31Transcript.successful_driver_has_trace
    (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
    Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances out selected hscan
  have htraceFull := AspisR1Query31DriverTraceScanOutV1.successful_driver_trace_scanOut
    blocks advances Query31ConcreteDriverTraceFacts.sourceDefaultState out selected
    (decodeState absorbed.state)
    Query31ConcreteDriverTraceFacts.sourceDefaultState_valid
    (by simpa [Query31ConcreteDriverTraceFacts.sourceDefaultState_maps_to_empty_q22])
    hdriverTrace
  have hdecodeStateEq : AspisV8R19.SqueezeOracleBridge.decodeState =
      AspisR1DigestLogCarrier.decodeState := by
    funext bytes
    rfl
  have hadvance : ∀ pair ∈ sourcePairs,
      decodeState pair.advance.output =
        SourceDigestOracle.oracle (p3PublicDigest32 sha256) absorbed.hash
          pubInput root length (FS2.Duplex.advanceA p (decodeState pair.state)) := by
    intro pair hmem
    exact (hfunctional pair hmem).2
  have hsourceFns := AspisR1.S4SourcePairsToFunctionsV1.sourcePair_functions_of_chain
    (D := p3PublicDigest32 sha256) (hash := absorbed.hash)
    absorbed sourcePairs hlen hfirst hchain
  have hsourceFns' := hsourceFns
  let blockFn : Nat → AspisV8R19.SourceDuplexStep.State :=
    fun k => decodeState (AspisR1.S4SourcePairsToFunctionsV1.sourcePairBlocks
      sourcePairs absorbed.state k)
  let stateFn : Nat → AspisV8R19.SourceDuplexStep.State :=
    fun k => decodeState (AspisR1.S4SourcePairsToFunctionsV1.sourcePairStates
      sourcePairs absorbed.state k)
  have hviews0 := AspisR1.S4PairFunctionViewsV1.materialized_pair_function_views
    sourcePairs absorbed.state blocks advances hmaterial
  have hviews :
      (R4Transport2QueryPrefix.pairs blockFn stateFn).map Prod.fst = blocks.val.map decodeState ∧
      (R4Transport2QueryPrefix.pairs blockFn stateFn).map Prod.snd = advances.val.map decodeState := by
    constructor
    · change (List.range 8).map blockFn = blocks.val.map decodeState
      exact hviews0.1.symm
    · change (List.range 8).map (fun k => stateFn (k+1)) = advances.val.map decodeState
      exact hviews0.2.symm
  have hpairScan := AspisR1.R4Transport2ScanComposition.eight_pairs_selected
    (R4Transport2QueryPrefix.pairs blockFn stateFn) (decodeState absorbed.state)
    (by simp [R4Transport2QueryPrefix.pairs])
  have htraceQ0 : R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0
      (blocks.val.map decodeState) (advances.val.map decodeState)
      (decodeState absorbed.state) =
      (.ok (out.val.map (fun w => w.val)), decodeState selected) := by
    simpa [Query31ConcreteDriverTraceFacts.sourceDefaultState_maps_to_empty_q22,
      R0C.V3.Q22.q0, hdecodeStateEq] using htraceFull
  have hpairFull : R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
      (R4Transport2QueryPrefix.pairs blockFn stateFn) (decodeState absorbed.state) =
      (.ok (out.val.map (fun w => w.val)), decodeState selected) := by
    calc
      _ = R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0
        (blocks.val.map decodeState) (advances.val.map decodeState)
        (decodeState absorbed.state) := by
          simpa [hviews.1, hviews.2] using hpairScan
      _ = _ := htraceQ0
  have hdigest : ∀ hash parts out,
      (p3PublicDigest32 sha256).digest hash parts = .ok out →
      decodeState out = hashBytes sha256 (flatten parts) := by
    intro hash parts out hd
    have hrecord := congrArg (fun d => d.digest hash parts)
      (p3_public_record_eq_model sha256)
    have hmodel : (S4SolanaDigestP3RegroupV1.solanaDigestP3Model
        solanaDigestCopyInst sha256).digest hash parts = .ok out := hrecord.symm.trans hd
    exact p3_success_interpreted solanaDigestCopyInst sha256 hash parts out hmodel
  have hliteralSource := AspisR1PublicPreparation.R4Transport2QueryAbsorb.source_query_prefix
    (p3PublicDigest32 sha256) self absorbed payload habs fits P
    (.payload (R4Transport2OpeningChain.message payload fits)) rfl hstate
    (AspisR1.S4SourcePairsToFunctionsV1.sourcePairBlocks sourcePairs absorbed.state)
    (AspisR1.S4SourcePairsToFunctionsV1.sourcePairStates sourcePairs absorbed.state)
    hsourceFns.1 hsourceFns.2.1 hsourceFns.2.2
    (fun bs => hashBytes sha256 bs) hdigest
  let H' : Addr SelectedTranscriptParams.L → State := fun a => hashBytes sha256 a.toBytes
  have hmap := congrArg Prod.snd
    (AspisR1.LiteralByteSampler.eval_eq (fun bs => hashBytes sha256 bs) 31 P
      (.payload (R4Transport2OpeningChain.message payload fits)))
  have hliteralEval :
      (AspisV8R19.MemoizedProgramLaw.eval (fun bs => hashBytes sha256 bs)
        (AspisR1.LiteralByteSampler.samp 31 P
          (.payload (R4Transport2OpeningChain.message payload fits))).toProgram).2 =
      UnifiedSampler.liftQuery (R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
        (R4Transport2QueryPrefix.pairs blockFn stateFn) (decodeState absorbed.state)) := by
    calc
      _ = (AspisV8R19.OracleProgramOps.mapView Addr.toBytes
        (AspisV8R19.MemoizedProgramLaw.eval H'
          (LiteralTranscript.samp 31 P
            (.payload (R4Transport2OpeningChain.message payload fits))).toProgram)).2 := hmap
      _ = _ := by
        simpa [AspisV8R19.OracleProgramOps.mapView, H', blockFn, stateFn, hsourceFns.1] using hliteralSource
  have hliteral :
      (AspisV8R19.MemoizedProgramLaw.eval (fun bs => hashBytes sha256 bs)
        (AspisR1.LiteralByteSampler.samp 31 P
          (.payload (R4Transport2OpeningChain.message payload fits))).toProgram).2 =
      (Value.queries (.ok (out.val.map (fun w => w.val))), decodeState after.state) := by
    rw [hliteralEval]
    rw [hpairFull]
    simp only [UnifiedSampler.liftQuery]
    rw [hafter]
  obtain ⟨q, hq, _⟩ := AspisR1.LiteralQuerySampleRunWitness.valid_row31_success_decodes_with_run
    (fun bs => hashBytes sha256 bs) P
    (R4Transport2OpeningChain.message payload fits)
    (out.val.map (fun w => w.val)) (decodeState after.state) hliteral
  refine ⟨hliteral, q, hq, ?_⟩
  intro j
  exact AspisR1.S4QueryArrayOrderV1.array_entry_eq_literal_query
    out (out.val.map (fun w => w.val)) q hq (by simp) j

#print axioms successful_queries_row31_literal_acceptance
end AspisR1.S4ChosenModelRow31AcceptanceV1
end
