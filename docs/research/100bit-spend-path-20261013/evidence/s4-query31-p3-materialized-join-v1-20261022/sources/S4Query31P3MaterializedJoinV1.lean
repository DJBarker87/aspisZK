import S4Query31MaterializedConditionalJoinV1
import S4SolanaDigestWrapperP3BindingV1
import S4P3SourceInterpretationV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section

namespace AspisR1.S4Query31P3MaterializedJoinV1
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
open S4SolanaDigestWrapperP3BindingV1
open AspisR1.S4P3SourceInterpretationV1

/-- The actual row-31 conditional materialized join specialized to the
    source-derived SolanaDigest wrapper under documented P3. Its digest
    interpretation is fixed to decode (sha256 (flatten parts)); the generic
    hdigest premise is discharged internally. No ROM property is asserted. -/
theorem actual_query_row31_solana_p3_materialized_join
    {M Cv : Type} {L : Nat}
    (B : QueriesModel.Boundaries)
    (sha256 : Bytes → Array U8 32#usize)
    (p : Params M Cv L) (pubInput : Slice U8) (root : Bytes32) (length : U32)
    (self after : transcript.Transcript SolanaDigest) (payload : Slice U8)
    (out : Array U32 22#usize)
    (hquery : QueriesModel.queries B (p3PublicDigest32 sha256) self
      31#u8 payload = ok (.Ok out, after))
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
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair (p3PublicDigest32 sha256) absorbed.hash), ∃ q,
      transcript.Transcript.absorb (p3PublicDigest32 sha256) self 31#u8 payload =
        ok absorbed ∧
      B.decode blocks advances = ok (.Ok (out, selected)) ∧
      after = {absorbed with state := selected} ∧
      pairs.length = 8 ∧
      LiteralQueryRead.decode xs = some q ∧
      (AspisR1.R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
        (R4Transport2QueryPrefix.pairs
          (fun k => decodeState (AspisR1.S4SourcePairsToFunctionsV1.sourcePairBlocks
            pairs absorbed.state k))
          (fun k => decodeState (AspisR1.S4SourcePairsToFunctionsV1.sourcePairStates
            pairs absorbed.state k)))
        (decodeState absorbed.state)).1 = .ok xs ∧
      blocks.val.map decodeState =
        QueryStateList.blocks p
          (SourceDigestOracle.oracle (p3PublicDigest32 sha256) absorbed.hash
            pubInput root length)
          (QuerySampler.state p
            (SourceDigestOracle.oracle (p3PublicDigest32 sha256) absorbed.hash
              pubInput root length)
            (decodeState absorbed.state)) 8 ∧
      advances.val.map decodeState =
        QueryStateList.advances
          (QuerySampler.state p
            (SourceDigestOracle.oracle (p3PublicDigest32 sha256) absorbed.hash
              pubInput root length)
            (decodeState absorbed.state)) 8 := by
  have hdigest : ∀ hash parts out,
      (p3PublicDigest32 sha256).digest hash parts = ok out →
      decodeState out = hashBytes sha256 (flatten parts) := by
    intro hash parts out hd
    have hrecord := congrArg (fun d => d.digest hash parts)
      (p3_public_record_eq_model sha256)
    have hmodel : (S4SolanaDigestP3RegroupV1.solanaDigestP3Model
        solanaDigestCopyInst sha256).digest hash parts = ok out :=
      hrecord.symm.trans hd
    exact p3_success_interpreted solanaDigestCopyInst sha256 hash parts out hmodel
  exact AspisR1.S4Query31MaterializedConditionalJoinV1.actual_query_row31_materialized_join
    B (p3PublicDigest32 sha256) p pubInput root length self after payload out hquery
    fits P hstate (fun bs => hashBytes sha256 bs) hdigest xs state hout

#print axioms actual_query_row31_solana_p3_materialized_join
end AspisR1.S4Query31P3MaterializedJoinV1
end
