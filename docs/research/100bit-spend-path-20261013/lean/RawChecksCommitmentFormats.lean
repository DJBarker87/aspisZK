import RawChecksConstructorScheduleV4
import R1LiteralSemanticCodecBridge
import R1LiteralOpeningPrefixFacts
import R1LiteralSemanticIndex
import R1LiteralMatchingFacts
import R1LiteralStageFacts
import R1LiteralReadAtFacts
import R1LiteralByteRunFacts
import RawCompiledTranscriptRoundAlignmentV7

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace AspisR1.RawChecksCommitmentFormats

open AspisR1.RawCutProverCompiler
open AspisR1.RawCutTranscriptRun
open AspisR1.RawCutWordsFromView
open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.LiteralTranscript
open AspisR1.LiteralOpeningView
open AspisR1.LiteralOpeningStages
open AspisR1.LiteralMatchingFacts
open AspisR1.LiteralSemanticCodecBridge
open AspisR1.LiteralSemanticIndex
open AspisR1.LiteralReadAtFacts
open AspisR1.SemanticRecordCodec
open AspisR1.OpeningRecordCodec
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State

private theorem take25_index_eq_full
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (hprefix : 2 < (rs.take 25).length) :
    (rs.take 25)[2]? = rs[2]? := by
  have happ := List.getElem?_append_left (l₂ := rs.drop 25) hprefix
  rw [List.take_append_drop 25 rs] at happ
  exact happ.symm

/-- The successful opening read strictly parses the row-2 C2 record, while
the successful matching read strictly parses the row-30 final-fold record.
This statement concerns the annotated protocol transcript. -/
theorem checks_give_commitment_parses
    (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (annotated : RunView)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (checks : LiteralAcceptanceTerminal.Checks annotated.2.1.1 rs)
    (hrows : rs = ((LiteralByteProtocol.protocol decoder).transcript H
      annotated.2.1.1 annotated.2.1.2 33).rounds) :
    (∃ root : State, ∃ b : LiteralTranscript.BytesMessage, ∃ w : LiteralTranscript.C2Word,
      annotated.2.1.2 2 = .c2 b w ∧
      SemanticRecordCodec.decode ⟨2, by decide⟩ b.val =
        some ⟨.c2Root root, by rfl⟩) ∧
    (∃ payload : OpeningRecordCodec.Payload .second,
      ∃ b : LiteralTranscript.BytesMessage, ∃ w : LiteralTranscript.VWord,
      annotated.2.1.2 30 = .second b w ∧
      OpeningRecordCodec.decode .second b.val = some payload) := by
  have hlength : ((LiteralByteProtocol.protocol decoder).transcript H
      annotated.2.1.1 annotated.2.1.2 33).rounds.length = 33 := by
    change ((LiteralByteProtocol.protocol decoder).transcript H
      annotated.2.1.1 annotated.2.1.2 33).round = 33
    exact LiteralByteRunFacts.transcript_round decoder H
      annotated.2.1.1 annotated.2.1.2 33
  have hlen : 32 ≤ rs.length := by rw [hrows, hlength]; omega
  have hvalid := RawChecksConstructorSchedule.checks_force_constructor_schedule
    annotated.2.1.1 rs checks hlen
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hcommon, hstaged, hrow31, hword, hgamma, hkappa, halpha0, halpha1, _⟩ :=
      LiteralMatchingFacts.read_success_components rs checks.data checks.matchingRead
  obtain ⟨hprefixLen, _hc1, _hc2, hsemantic, _hword⟩ :=
    LiteralOpeningPrefixFacts.read_prefix_components rs common hcommon
  have hiSmall : 2 < (rs.take 25).length := by rw [hprefixLen]; omega
  have hsmallGet := take25_index_eq_full rs hiSmall
  have hidx2 := LiteralByteRunFacts.transcript_index decoder H
    annotated.2.1.1 annotated.2.1.2 33 2 (by omega)
  rw [← hrows] at hidx2
  have hreadIdx := LiteralSemanticIndex.read_index LiteralOpeningView.eK 0
    (rs.take 25) common.semantic hsemantic
  obtain ⟨hrow2, parsed2, challenge2, hparse2, _hchallenge2, _hout2⟩ :=
    hreadIdx 2 hiSmall
  have htakeVal : (rs.take 25)[2]? = some ((rs.take 25)[2]'hiSmall) :=
    List.getElem?_eq_getElem hiSmall
  have hfullVal : rs[2]? = some ((rs.take 25)[2]'hiSmall) := hsmallGet.symm.trans htakeVal
  have hrowEq2 : (rs.take 25)[2]'hiSmall =
      (annotated.2.1.2 2,
        (eval H (LiteralByteSampler.samp 2
          ((LiteralByteProtocol.protocol decoder).transcript H
            annotated.2.1.1 annotated.2.1.2 2)
          (annotated.2.1.2 2)).toProgram).2) :=
    Option.some.inj (hfullVal.symm.trans hidx2)
  have hvalidPair2 := hvalid 2 (by omega)
  obtain ⟨m2, c2, hentry2, hv2⟩ := hvalidPair2
  have hpair2 := Option.some.inj (hentry2.symm.trans hidx2)
  have hm2 : m2 = annotated.2.1.2 2 := congrArg Prod.fst hpair2
  have hshape2 : ∃ b w, m2 = .c2 b w := by
    cases m2 <;> simp [LiteralTranscript.valid] at hv2 ⊢
  obtain ⟨b2, w2, hb2m⟩ := hshape2
  have hb2 : annotated.2.1.2 2 = .c2 b2 w2 := by rw [← hm2, hb2m]
  have htakeMsg : ((rs.take 25)[2]'hiSmall).1 = .c2 b2 w2 := by
    rw [congrArg Prod.fst hrowEq2, hb2]
  have hparse2' : LiteralSemanticPrefix.parseMessage LiteralOpeningView.eK
      ⟨2, hrow2⟩ (.c2 b2 w2) = some parsed2 := by
    rw [htakeMsg] at hparse2
    exact hparse2
  obtain ⟨decoded2, hdecode2⟩ := LiteralSemanticCodecBridge.decode_of_parseMessage
    LiteralOpeningView.eK ⟨2, hrow2⟩ (.c2 b2 w2) parsed2 hparse2'
  have hdecode2' : SemanticRecordCodec.decode ⟨2, by decide⟩ b2.val = some decoded2 := by
    simpa only [LiteralSemanticCodecBridge.record] using hdecode2
  have hc2decode : ∃ root : State,
      SemanticRecordCodec.decode ⟨2, by decide⟩ b2.val =
        some ⟨.c2Root root, by rfl⟩ := by
    rcases decoded2 with ⟨value, hvalue⟩
    cases value with
    | empty => simp [SemanticRecordCodec.validRow] at hvalue
    | c2Root root => exact ⟨root, hdecode2'⟩
    | maskSum x => simp [SemanticRecordCodec.validRow] at hvalue
    | polynomial x => simp [SemanticRecordCodec.validRow] at hvalue
  have hread30 := LiteralReadAtFacts.readSecond_current rs staged hstaged
  have hidx30 := LiteralByteRunFacts.transcript_index decoder H
    annotated.2.1.1 annotated.2.1.2 33 30 (by omega)
  rw [← hrows] at hidx30
  have hvalidPair30 := hvalid 30 (by omega)
  obtain ⟨m30, c30, hentry30, hv30⟩ := hvalidPair30
  have hpair30 := Option.some.inj (hentry30.symm.trans hidx30)
  have hm30 : m30 = annotated.2.1.2 30 := congrArg Prod.fst hpair30
  have hshape30 : ∃ b w, m30 = .second b w := by
    cases m30 <;> simp [LiteralTranscript.valid] at hv30 ⊢
  obtain ⟨b30, w30, hb30m⟩ := hshape30
  have hb30 : annotated.2.1.2 30 = .second b30 w30 := by rw [← hm30, hb30m]
  have hdecode30 : OpeningRecordCodec.decode .second b30.val = some staged.row30 := by
    unfold LiteralOpeningStages.readAt at hread30
    rw [hidx30, hb30] at hread30
    simpa [LiteralTranscript.valid, LiteralTranscript.erase] using hread30
  exact ⟨⟨Classical.choose hc2decode, b2, w2, hb2, Classical.choose_spec hc2decode⟩,
    ⟨staged.row30, b30, w30, hb30, hdecode30⟩⟩

#print axioms checks_give_commitment_parses
end AspisR1.RawChecksCommitmentFormats
end
