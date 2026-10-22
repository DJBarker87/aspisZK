import S4LiteralRow31PairsJoinV1
import S4QueryArrayViewsV1
import S4SourcePairsToFunctionsV1
import Query31MathematicalSchedule

open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section

namespace AspisR1.S4Query31MaterializedConditionalJoinV1
open AspisR1PublicPreparation
open AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1PublicPreparation.R4Transport2QueryAbsorb
open AspisR1PublicPreparation.R4Transport2OpeningChain
open AspisR1.R4Transport2ScanComposition
open AspisR1PublicPreparation.R4Transport2QueryPrefix
open AspisR1PublicPreparation.TranscriptStep
open AspisR1PublicPreparation.SourceDigestOracle
open AspisR1.LiteralQuerySampleRunWitness
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep FS2.Duplex
open AspisV8R19.SqueezeOracleBridge
open AspisR1.QuerySampler AspisR1.QueryStateList

/-- Conditional row-31 sampler output, tied to the exact same source pairs and
the two arrays produced by the successful extracted queries operation. The
initial transcript-byte interpretation is retained explicitly as `hdigest`;
no generic Digest32 grouping law or authentication statement is added. -/
theorem actual_query_row31_materialized_join
    {Hash M Cv : Type} {L : Nat}
    (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 Hash)
    (p : Params M Cv L) (pubInput : Slice U8) (root : Bytes32) (length : U32)
    (self after : transcript.Transcript Hash) (payload : Slice U8)
    (out : Array U32 22#usize)
    (hquery : QueriesModel.queries B D self 31#u8 payload = ok (.Ok out,after))
    (fits : (R4Transport2OpeningChain.framed payload).length ≤ SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts))
    (xs : List Nat) (state : State)
    (hout : (AspisV8R19.MemoizedProgramLaw.eval H
      (AspisR1.LiteralByteSampler.samp 31 P
        (.payload (R4Transport2OpeningChain.message payload fits))).toProgram).2 =
      (AspisR1.TranscriptView.Value.queries (.ok xs),state)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash), ∃ q,
      transcript.Transcript.absorb D self 31#u8 payload = ok absorbed ∧
      B.decode blocks advances = ok (.Ok (out,selected)) ∧
      after = {absorbed with state := selected} ∧
      pairs.length = 8 ∧
      LiteralQueryRead.decode xs = some q ∧
      (AspisR1.R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
        (R4Transport2QueryPrefix.pairs
          (fun k => decodeState (AspisR1.S4SourcePairsToFunctionsV1.sourcePairBlocks pairs absorbed.state k))
          (fun k => decodeState (AspisR1.S4SourcePairsToFunctionsV1.sourcePairStates pairs absorbed.state k)))
        (decodeState absorbed.state)).1 = .ok xs ∧
      blocks.val.map decodeState =
        QueryStateList.blocks p
          (SourceDigestOracle.oracle D absorbed.hash pubInput root length)
          (QuerySampler.state p
            (SourceDigestOracle.oracle D absorbed.hash pubInput root length)
            (decodeState absorbed.state)) 8 ∧
      advances.val.map decodeState =
        QueryStateList.advances
          (QuerySampler.state p
            (SourceDigestOracle.oracle D absorbed.hash pubInput root length)
            (decodeState absorbed.state)) 8 := by
  obtain ⟨absorbed,blocks,advances,selected,pairs,habs,hdecode,hafter,hlen,
      hfirst,hchain,hfunctional,hmaterial⟩ :=
    queries_success_pairs_functional_full B D p pubInput root length self after
      31#u8 payload out hquery
  rcases hfirst with ⟨first,rest,hpairs,hfirstState⟩
  subst pairs
  have hadvance : ∀ pair ∈ first :: rest,
      decodeState pair.advance.output =
        SourceDigestOracle.oracle D absorbed.hash pubInput root length
          (advanceA p (decodeState pair.state)) := by
    intro pair hmem
    exact (hfunctional pair hmem).2
  have haligned := stateChain_alignedStates p
    (SourceDigestOracle.oracle D absorbed.hash pubInput root length)
    first rest hchain hadvance
  have hmap := alignedStates_map_eq_querySampler p
    (SourceDigestOracle.oracle D absorbed.hash pubInput root length)
    (decodeState first.state) (first :: rest) haligned
  have hfirstDecode : decodeState first.state = decodeState absorbed.state :=
    congrArg decodeState hfirstState
  rw [hfirstDecode] at hmap
  have hstates : (first :: rest).map (fun pair => decodeState pair.state) =
      (List.range (first :: rest).length).map
        (fun i => QuerySampler.state p
          (SourceDigestOracle.oracle D absorbed.hash pubInput root length)
          (decodeState absorbed.state) i) := by
    simpa using hmap
  have hsourceFns := AspisR1.S4SourcePairsToFunctionsV1.sourcePair_functions_of_chain
    (H := Hash) (D := D) (hash := absorbed.hash)
    absorbed (first :: rest) hlen ⟨first,rest,rfl,hfirstState⟩ hchain
  have harrayviews := AspisR1.S4QueryArrayViewsV1.materialized_pair_views
    p (SourceDigestOracle.oracle D absorbed.hash pubInput root length)
    (decodeState absorbed.state) (first :: rest) blocks advances hmaterial hlen
    hstates hfunctional
  have hrow := AspisR1.S4LiteralRow31PairsJoinV1.row31_success_list_eq_source_pairs
    D self absorbed payload habs fits P hstate
    (AspisR1.S4SourcePairsToFunctionsV1.sourcePairBlocks (first :: rest) absorbed.state)
    (AspisR1.S4SourcePairsToFunctionsV1.sourcePairStates (first :: rest) absorbed.state)
    hsourceFns.1 hsourceFns.2.1 hsourceFns.2.2 H hdigest xs state hout
  rcases hrow with ⟨q,hq,hscan⟩
  exact ⟨absorbed,blocks,advances,selected,first::rest,q,
    habs,hdecode,hafter,hlen,hq,hscan,harrayviews.1,harrayviews.2⟩

#print axioms actual_query_row31_materialized_join
end AspisR1.S4Query31MaterializedConditionalJoinV1
end
