import RawCutRecordedWordsExecutable
import RawCommitmentFrameReplay
import RawCutWordsFromView
import GSByteJointSpendExtractor
import ExactBaseProjection
import LiteralSemanticView
import LiteralTypedWords
import RawCutProverCompiler

set_option autoImplicit false
namespace AspisR1.RawCutWordsFromRunExecutable

open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.RawCutRecordedWordsExecutable
open AspisR1.RawCommitmentFrameReplay
open AspisR1.RawCutProverCompiler
open AspisR1.GSByteJointSpendExtractor
open AspisR1.LiteralTranscript

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
  LiteralTypedWords.word ExactBaseProjection.embed LiteralSemanticView.eK
    (wordsFromRun run).c1 (wordsFromRun run).c2

/-- The fixed final word consumed by the same extractor is the recovered
folded commitment word. -/
def finalWordFromRun (run : RunView) : FinalWord AspisWideTower.WideExact :=
  (wordsFromRun run).final

/-- Actual fixed-word extractor caller on the words recovered from this run.
This definition does not assert that those words are already the generated
prover inputs; that is supplied by the explicit frame-compatibility theorem. -/
def extractFromRun (pub : R0P.Public M31Exact) (run : RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) : Option Wspend :=
  GSByteJointSpendExtractor.extract pub (initialWordsFromRun run)
    (fun _ => finalWordFromRun run) coins

/-- Validity is stated on the real proof rows through the final commitment
cut. The frame correspondence remains an explicit source-replay contract. -/
def ValidPrefix (run : RunView) : Prop :=
  ∀ row, row ≤ 30 → LiteralTranscript.valid row (run.2.1.2 row)

def FrameCompatible (decoder : LiteralByteProtocol.Decoder) (run : RunView) : Prop :=
  ∀ row, row ≤ 30 →
    LiteralTranscript.valid row (run.2.1.2 row) →
    RawCommitmentFrameReplay.frameFromView run row =
      RawCutWordsFromView.frameFromView decoder run row

/-- Once the transcript replay supplies actual frame bytes for valid rows,
the executable raw-word construction is exactly the existing caller's
recorded-cut constructor. No equality of recovered words is postulated. -/
theorem wordsFromRun_eq_buildWords (decoder : LiteralByteProtocol.Decoder)
    (run : RunView) (hvalid : ValidPrefix run)
    (hframes : FrameCompatible decoder run) :
    wordsFromRun run = RawCutWordsFromView.buildWords decoder run := by
  unfold wordsFromRun RawCutWordsFromView.buildWords
  have h0 := hframes 0 (by omega) (hvalid 0 (by omega))
  have h2 := hframes 2 (by omega) (hvalid 2 (by omega))
  have h30 := hframes 30 (by omega) (hvalid 30 (by omega))
  simp only [RawCutWordsFromView.frameFromView] at h0 h2 h30
  rw [h0, h2, h30]
  rfl

#print axioms wordsFromRun
#print axioms initialWordsFromRun
#print axioms finalWordFromRun
#print axioms extractFromRun
#print axioms wordsFromRun_eq_buildWords
end AspisR1.RawCutWordsFromRunExecutable
