import RPz8_SCF_Deletion
import OraclePortRefineJoinExtractionTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCF_Recovery
open RawCutWordsFromRunExecutableBin
open OraclePortRefineJoin

/-- Exact maintained recovered-input interface, derived from causal cuts and
semantic public equality. No equality of whole logs is required. -/
theorem agreement (left right : RawCutProverCompiler.RunView)
    (pub : left.2.1.1 = right.2.1.1)
    (frames : ∀ row, row = 0 ∨ row = 2 ∨ row = 30 →
      RawCommitmentFrameReplay.frameFromView left row =
        RawCommitmentFrameReplay.frameFromView right row)
    (cuts : ∀ row, row = 0 ∨ row = 2 ∨ row = 30 →
      BinRawByteCutRecovery.cut left.1 (RawCommitmentFrameReplay.frameFromView right row) =
        BinRawByteCutRecovery.cut right.1 (RawCommitmentFrameReplay.frameFromView right row)) :
    RecoveredInputAgreement left right := by
  have words := SCF_Cuts.recovered left right frames cuts
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun p : LiteralTranscript.Public => SemanticPublicWire.parsePublic p.pubBytes) pub
  · unfold initialWordsFromRun
    rw [words]
  · exact congrArg CanonicalCutEnrichedTranscript.Words.final words

/-- Each private extractor coin tape is preserved by the exact interface. -/
theorem extract (left right : RawCutProverCompiler.RunView)
    (agree : RecoveredInputAgreement left right)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    RawRecordedPublicSpendExtractorBin.extract left coins =
      RawRecordedPublicSpendExtractorBin.extract right coins :=
  extractor_eq_of_recovered_inputs left right agree coins

#print axioms agreement
#print axioms extract
end AspisR1.SCF_Recovery
end
