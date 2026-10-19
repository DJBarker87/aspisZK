import RawCutRecordedWordsExecutable
import RawCommitmentFrameReplay
import RawCommitmentFrameReplayCorrect
import RawCutWordsFromView
import GSByteJointSpendExtractor
import R1ExactBaseProjection
import R1LiteralSemanticView
import R1LiteralTypedWords
import RawCutProverCompiler

set_option autoImplicit false
namespace AspisR1.RawCutWordsFromRunExecutable

open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.RawCutRecordedWordsExecutable
open AspisR1.RawCommitmentFrameReplay
open AspisR1.RawCutProverCompiler
open AspisR1.GSByteJointSpendExtractor
open AspisR1.LiteralTranscript
open AspisPool.AlgorithmicCircleDecoderV7 AspisV8R15.ExactTowerBase SpendRelation

abbrev RunView := RawCutProverCompiler.RunView
abbrev Words := CanonicalCutEnrichedTranscript.Words

/-- Executable metadata recovery from the recorded run.  The source rows are
read from the actual run log; only the three commitment frame byte strings
come from the explicit transcript-state replay. -/
def wordsFromRun (run : RunView) : Words :=
  wordsFromRecordedLogExec run.1
    (RawCommitmentFrameReplay.frameFromView run 0)
    (RawCommitmentFrameReplay.frameFromView run 2)
    (RawCommitmentFrameReplay.frameFromView run 30)

/-- The 29 fixed initial words that the maintained byte-GS extractor consumes,
constructed from the recovered typed C1/C2 maps. -/
def initialWordsFromRun (run : RunView) : Fin 29 → InitialWord AspisWideTower.WideExact :=
  LiteralTypedWords.word ExactBaseProjection.embed
    (algebraMap QM31Exact AspisWideTower.WideExact)
    (wordsFromRun run).c1 (wordsFromRun run).c2

/-- The fixed final word consumed by the same extractor is the recovered
folded commitment word. -/
def finalWordFromRun (run : RunView) : FinalWord AspisWideTower.WideExact :=
  (wordsFromRun run).final

/-- Actual fixed-word extractor caller on the words recovered from this run.
This definition does not assert that those words are already the generated
prover inputs; that is supplied by the checked frame-replay theorem below. -/
def extractFromRun (pub : R0P.Public M31Exact) (run : RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) : Option Wspend :=
  GSByteJointSpendExtractor.extract pub (initialWordsFromRun run)
    (fun _ => finalWordFromRun run) coins

/-- Validity is stated on the real proof rows through the final commitment
cut and is the sole premise needed by the checked frame-replay theorem. -/
def ValidPrefix (run : RunView) : Prop :=
  ∀ row, row ≤ 30 → LiteralTranscript.valid row (run.2.1.2 row)

/-- The checked transcript replay supplies the frame bytes at rows 0, 2, and
30, so the executable raw-word construction is exactly the recorded-cut
constructor. No frame-compatibility hypothesis is postulated. -/
theorem wordsFromRun_eq_buildWords (decoder : LiteralByteProtocol.Decoder)
    (run : RunView) (hvalid : ValidPrefix run) :
    wordsFromRun run = RawCutWordsFromView.buildWords decoder run := by
  unfold wordsFromRun RawCutWordsFromView.buildWords
  obtain ⟨h0, h2, h30⟩ :=
    RawCommitmentFrameReplayCorrect.frameFromView_commitments_eq decoder run hvalid
  simp only [RawCutWordsFromView.frameFromView] at h0 h2 h30
  rw [h0, h2, h30]
  rw [RawCutRecordedWordsExecutable.wordsFromRecordedLogExec_eq_wordsFromRawCuts]
  simp only [RawCutWordsFromView.rootFrom,
    RawCutRecordedWordsExecutable.rootFromExec]
  rfl

#print axioms wordsFromRun
#print axioms initialWordsFromRun
#print axioms finalWordFromRun
#print axioms extractFromRun
#print axioms wordsFromRun_eq_buildWords
end AspisR1.RawCutWordsFromRunExecutable
