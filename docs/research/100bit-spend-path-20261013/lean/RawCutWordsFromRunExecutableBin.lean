import BinCompiledRunWordStability
import BinThreeCommitmentTypedOpening
import BinRecordedRecoveryWitness
import SharedBinaryRecordGrammar
import RawCutRecordedWordsExecutableBin
import RawCommitmentFrameReplay
import RawCommitmentFrameReplayCorrect
import RawCutWordsFromView
import GSByteJointSpendExtractor
import R1ExactBaseProjection
import R1LiteralSemanticView
import R1LiteralTypedWords
import RawCutProverCompiler

set_option autoImplicit false
namespace AspisR1.RawCutWordsFromRunExecutableBin

open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.RawCutRecordedWordsExecutable
open AspisR1.RawCommitmentFrameReplay
open AspisR1.RawCutProverCompiler
open AspisR1.GSByteJointSpendExtractor
open AspisR1.LiteralTranscript
open AspisPool.AlgorithmicCircleDecoderV7 AspisV8R15.ExactTowerBase SpendRelation

abbrev RunView := RawCutProverCompiler.RunView
abbrev Words := CanonicalCutEnrichedTranscript.Words

/-- Binary recovery at the actual replayed commitment cuts. The maps use
strict two-child nodes and eighteen binary slots; typed projections are shared. -/
def wordsFromRun (run : RunView) : Words :=
  let f0 := RawCommitmentFrameReplay.frameFromView run 0
  let f2 := RawCommitmentFrameReplay.frameFromView run 2
  let f30 := RawCommitmentFrameReplay.frameFromView run 30
  RawCutRecordedWordsExecutableBin.wordsFromRecordedCutsExec run.1 f0 f2 f30
    (RawCutWordsFromView.rootFrom 8 f0) (RawCutWordsFromView.rootFrom 8 f2)
    (RawCutWordsFromView.rootFrom 9 f30)

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
    wordsFromRun run = BinCompiledRunWordStability.wordsFromRun decoder run := by
  unfold wordsFromRun BinCompiledRunWordStability.wordsFromRun
  rw [RawCutRecordedWordsExecutableBin.wordsFromRecordedCutsExec_eq_wordsFromRawCuts]
  obtain ⟨h0, h2, h30⟩ :=
    RawCommitmentFrameReplayCorrect.frameFromView_commitments_eq decoder run hvalid
  simp only [RawCutWordsFromView.frameFromView] at h0 h2 h30
  rw [h0, h2, h30]
  rfl

#print axioms wordsFromRun
#print axioms initialWordsFromRun
#print axioms finalWordFromRun
#print axioms extractFromRun
#print axioms wordsFromRun_eq_buildWords
end AspisR1.RawCutWordsFromRunExecutableBin
