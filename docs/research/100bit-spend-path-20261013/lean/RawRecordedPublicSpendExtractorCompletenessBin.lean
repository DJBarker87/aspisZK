import RawRecordedPublicSpendExtractorReturnedRelationBin
import RawRecordedChecksSpendExtractorBin

/-! Completeness of the ordinary parser-inclusive recorded-run extractor.
Production acceptance-to-Checks remains explicit through the checks input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.RawRecordedPublicSpendExtractorBin
open AspisR1.LiteralTranscript AspisR1.RawCutWordsFromRunExecutableBin
open AspisR1.RawCutWordsFromRunPublicValidBin
open AspisR1.GSByteJointSpendExtractor
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

attribute [local irreducible] RawCutWordsFromRunExecutableBin.extractFromRun
  GSByteJointSpendExtractor.extract runDecodedPublic

/-- With terminal checks, no classifier hit and a successful actual byte
bank, this run-and-coins-only extractor returns a valid public-byte witness. -/
theorem extract_of_checks_noHit_bank
    (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (H : Bytes → AspisR1.LiteralByteProtocol.State)
    (run : RawCutProverCompiler.RunView)
    (checks : LiteralAcceptanceTerminal.Checks run.2.1.1
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
        (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad run.2.1.1 []
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
        (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds)
    (coins : Coins)
    (hbank : ¬ AspisR1.GSConcreteByteDecoderBank.failed
      (AspisWide.GSConcreteReceivedWordInputs.fromWords (initialWordsFromRun run)
        (fun _ => finalWordFromRun run)) coins) :
    ∃ witness,
      extract run coins = some witness ∧
      LiteralProtocol.relation run.2.1.1 witness := by
  obtain ⟨w, hw, _⟩ :=
    RawRecordedChecksSpendExtractorBin.extractFromRun_of_checks_noHit_bank
      decoder H run checks hno coins hbank
  have hpublic : runDecodedPublic run = some checks.decoded := by
    unfold RawCutWordsFromRunPublicValidBin.runDecodedPublic
    exact checks.publicParsed
  have hextract : extract run coins = some w :=
    (extract_eq_of_public_parse run checks.decoded coins hpublic).trans hw
  exact ⟨w, hextract, returned_relation run coins w hextract⟩

#print axioms extract_of_checks_noHit_bank
end AspisR1.RawRecordedPublicSpendExtractorBin
end
