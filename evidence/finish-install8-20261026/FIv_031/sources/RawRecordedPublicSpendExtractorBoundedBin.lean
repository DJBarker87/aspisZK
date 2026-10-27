import RawCutRecordedWordsBoundedBin
import RawRecordedPublicSpendExtractorCompletenessBin

/-! Bounded leaf parsing is substituted throughout all three recovered maps.
Every equality is total, including malformed inputs and private-tape aborts. -/
set_option autoImplicit false
namespace AspisR1.RawRecordedPublicSpendExtractorBoundedBin
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.SpendRelation AspisV8R15.ExactTowerBase
abbrev RunView := RawCutProverCompiler.RunView
abbrev Coins := GSConcreteByteDecoderBank.RawCoins

def wordsFromRun (run : RunView) : Words :=
  let f0 := RawCommitmentFrameReplay.frameFromView run 0
  let f2 := RawCommitmentFrameReplay.frameFromView run 2
  let f30 := RawCommitmentFrameReplay.frameFromView run 30
  RawCutRecordedWordsBoundedBin.wordsFromRecordedCutsExec run.1 f0 f2 f30
    (RawCutWordsFromView.rootFrom 8 f0) (RawCutWordsFromView.rootFrom 8 f2)
    (RawCutWordsFromView.rootFrom 9 f30)

theorem words_value (run : RunView) :
    wordsFromRun run = RawCutWordsFromRunExecutableBin.wordsFromRun run := by
  unfold wordsFromRun RawCutWordsFromRunExecutableBin.wordsFromRun
  rw [RawCutRecordedWordsBoundedBin.wordsFromRecordedCutsExec_eq_wordsFromRawCuts,
    RawCutRecordedWordsExecutableBin.wordsFromRecordedCutsExec_eq_wordsFromRawCuts]

def initialWordsFromRun (run : RunView) :=
  LiteralTypedWords.word ExactBaseProjection.embed
    (algebraMap QM31Exact AspisWideTower.WideExact)
    (wordsFromRun run).c1 (wordsFromRun run).c2

def finalWordFromRun (run : RunView) := (wordsFromRun run).final

theorem initial_value (run : RunView) : initialWordsFromRun run =
    RawCutWordsFromRunExecutableBin.initialWordsFromRun run := by
  unfold initialWordsFromRun RawCutWordsFromRunExecutableBin.initialWordsFromRun
  rw [words_value]

theorem final_value (run : RunView) : finalWordFromRun run =
    RawCutWordsFromRunExecutableBin.finalWordFromRun run := by
  unfold finalWordFromRun RawCutWordsFromRunExecutableBin.finalWordFromRun
  rw [words_value]

def extract (run : RunView) (coins : Coins) : Option Wspend :=
  (RawCutWordsFromRunPublicValidBin.runDecodedPublic run).bind fun decoded =>
    GSByteJointSpendExtractor.extract decoded (initialWordsFromRun run)
      (fun _ => finalWordFromRun run) coins

theorem value (run : RunView) (coins : Coins) : extract run coins =
    RawRecordedPublicSpendExtractorBin.extract run coins := by
  unfold extract RawRecordedPublicSpendExtractorBin.extract
    RawCutWordsFromRunExecutableBin.extractFromRun
  rw [initial_value, final_value]

theorem returned_relation (run : RunView) (coins : Coins) (w : Wspend)
    (h : extract run coins = some w) : LiteralProtocol.relation run.2.1.1 w :=
  RawRecordedPublicSpendExtractorBin.returned_relation run coins w
    ((value run coins).symm.trans h)

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
  rw [words_value] at checks hno
  rw [initial_value, final_value] at hbank
  obtain ⟨w, hw, hr⟩ := RawRecordedPublicSpendExtractorBin.extract_of_checks_noHit_bank
    decoder H run checks hno coins hbank
  exact ⟨w, (value run coins).trans hw, hr⟩

#print axioms words_value
#print axioms initial_value
#print axioms final_value
#print axioms value
#print axioms returned_relation
#print axioms extract_of_checks_noHit_bank
end AspisR1.RawRecordedPublicSpendExtractorBoundedBin
