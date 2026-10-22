import Query31SourceOracleBridge
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
open AspisR1.QuerySampler AspisR1.QueryStateList
open S4SolanaDigestWrapperP3BindingV1
open AspisR1.S4P3SourceInterpretationV1
set_option autoImplicit false
noncomputable section

namespace AspisR1.S4ChosenModelRow31QueryV1

theorem successful_queries_row31_literal_coordinates
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
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (xs : List Nat) (state : State)
    (hout : (AspisV8R19.MemoizedProgramLaw.eval
      (fun bs => hashBytes sha256 bs)
      (AspisR1.LiteralByteSampler.samp 31 P
        (.payload (R4Transport2OpeningChain.message payload fits))).toProgram).2 =
      (AspisR1.TranscriptView.Value.queries (.ok xs), state)) :
    ∃ q, LiteralQueryRead.decode xs = some q ∧
      ∀ j : Fin 22, (out.val[j.val]'(by scalar_tac)).val = (q j).val := by
  let B := Query31ConcreteMaterializedSchedule.concreteBoundaries
    Query31ConcreteDriverTraceFacts.sourceDefaultState embed
  obtain ⟨absorbed, blocks, advances, selected, sourcePairs,
      habs, hdecode, hafter, hlen, hfirst, hchain, hfunctional, hmaterial⟩ :=
    AspisR1PublicPreparation.Query31SourceSchedule.queries_success_pairs_functional_full
      B (p3PublicDigest32 sha256) p pubInput root length self after 31#u8 payload out hquery
  let decodeBlock := Query31ConcreteWordsDriverChain.actualQueryWords
  have hdecoded : Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances =
        .ok (.Ok (out, selected)) := by
    change Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances = _
    exact hdecode
  have hscan := Query31ConcreteMaterializedSchedule.adaptScanResult_success hdecoded
  let trace := AspisR1Query31Transcript.successful_driver_has_trace
    (Query31ModelScanCall.modelScanFn decodeBlock)
    Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances out selected hscan
  have htrace := AspisR1Query31DriverTraceScanOutV1.successful_driver_trace_scanOut
    blocks advances Query31ConcreteDriverTraceFacts.sourceDefaultState out selected
    (decodeState absorbed.state)
    Query31ConcreteDriverTraceFacts.sourceDefaultState_valid
    (by simpa [Query31ConcreteDriverTraceFacts.sourceDefaultState_maps_to_empty_q22])
    trace
  have hdecodeStateEq : AspisV8R19.SqueezeOracleBridge.decodeState =
      AspisR1DigestLogCarrier.decodeState := by
    funext bytes
    rfl
  have htraceOut :
      (R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0
        (blocks.val.map AspisV8R19.SqueezeOracleBridge.decodeState)
        (advances.val.map AspisV8R19.SqueezeOracleBridge.decodeState)
        (AspisV8R19.SqueezeOracleBridge.decodeState absorbed.state)).1 =
          .ok (out.val.map (fun w => w.val)) := by
    simpa [Query31ConcreteDriverTraceFacts.sourceDefaultState_maps_to_empty_q22,
      R0C.V3.Q22.q0, hdecodeStateEq] using
      congrArg Prod.fst htrace
  rcases hfirst with ⟨first, rest, hpairs, hfirstState⟩
  subst sourcePairs
  have hadvance : ∀ pair ∈ first :: rest,
      decodeState pair.advance.output =
        SourceDigestOracle.oracle (p3PublicDigest32 sha256) absorbed.hash
          pubInput root length (FS2.Duplex.advanceA p (decodeState pair.state)) := by
    intro pair hmem
    exact (hfunctional pair hmem).2
  have haligned := AspisR1PublicPreparation.Query31SourceSchedule.stateChain_alignedStates
    p (SourceDigestOracle.oracle (p3PublicDigest32 sha256) absorbed.hash pubInput root length)
    first rest hchain hadvance
  have hmap := AspisR1PublicPreparation.Query31SourceSchedule.alignedStates_map_eq_querySampler
    p (SourceDigestOracle.oracle (p3PublicDigest32 sha256) absorbed.hash pubInput root length)
    (decodeState first.state) (first :: rest) haligned
  have hstart : decodeState first.state = decodeState absorbed.state :=
    congrArg decodeState hfirstState
  rw [hstart] at hmap
  have hstates : (first :: rest).map (fun pair => decodeState pair.state) =
      (List.range (first :: rest).length).map
        (fun i => QuerySampler.state p
          (SourceDigestOracle.oracle (p3PublicDigest32 sha256) absorbed.hash
            pubInput root length)
          (decodeState absorbed.state) i) := by
    simpa using hmap
  have hsourceFns := AspisR1.S4SourcePairsToFunctionsV1.sourcePair_functions_of_chain
    (H := SolanaDigest) (D := p3PublicDigest32 sha256) (hash := absorbed.hash)
    absorbed (first :: rest) hlen ⟨first, rest, rfl, hfirstState⟩ hchain
  have hdigest : ∀ hash parts out,
      (p3PublicDigest32 sha256).digest hash parts = .ok out →
      decodeState out = hashBytes sha256 (flatten parts) := by
    intro hash parts out hd
    have hrecord := congrArg (fun d => d.digest hash parts)
      (p3_public_record_eq_model sha256)
    have hmodel : (S4SolanaDigestP3RegroupV1.solanaDigestP3Model
        solanaDigestCopyInst sha256).digest hash parts = .ok out := hrecord.symm.trans hd
    exact p3_success_interpreted solanaDigestCopyInst sha256 hash parts out hmodel
  obtain ⟨q, hq, hpairsRun⟩ :=
    AspisR1.S4LiteralRow31PairsJoinV1.row31_success_list_eq_source_pairs
      (p3PublicDigest32 sha256) self absorbed payload habs fits P hstate
      (AspisR1.S4SourcePairsToFunctionsV1.sourcePairBlocks (first :: rest) absorbed.state)
      (AspisR1.S4SourcePairsToFunctionsV1.sourcePairStates (first :: rest) absorbed.state)
      hsourceFns.1 hsourceFns.2.1 hsourceFns.2.2
      (fun bs => hashBytes sha256 bs) hdigest xs state hout
  have horder := AspisR1.S4Row31SourceTraceConsumerV1.row31_source_trace_output
    (first :: rest) absorbed.state blocks advances xs out hmaterial hpairsRun htraceOut
  refine ⟨q, hq, ?_⟩
  intro j
  exact AspisR1.S4QueryArrayOrderV1.array_entry_eq_literal_query out xs q hq horder j

#print axioms successful_queries_row31_literal_coordinates
end AspisR1.S4ChosenModelRow31QueryV1
end
