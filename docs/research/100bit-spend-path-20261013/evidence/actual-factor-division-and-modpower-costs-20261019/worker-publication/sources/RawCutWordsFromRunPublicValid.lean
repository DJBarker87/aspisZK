import RawCutWordsFromRunExecutable
import R1SemanticPublicWire
import GSByteJointSpendExtractor

set_option autoImplicit false
namespace AspisR1.RawCutWordsFromRunPublicValid

open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.GSByteJointSpendExtractor
open AspisR1.SemanticPublicWire
open AspisR1.RawCutProverCompiler
open AspisR1.SpendRelation
open AspisV8R15.ExactTowerBase

abbrev RunView := RawCutProverCompiler.RunView

/-- The semantic public supplied to the fixed-word extractor is explicitly
the public parsed from the public bytes in the recorded prover run. -/
def runDecodedPublic (run : RunView) : Option (R0P.Public M31Exact) :=
  SemanticPublicWire.parsePublic run.2.1.1.pubBytes

/-- Any successful run-based extraction returns a valid spend witness for
the supplied decoded public.  The first conjunct records the precise relation
between that public and the recorded run; this theorem makes no claim that
the source itself was accepted or that its rows are valid. -/
theorem extractFromRun_returned_valid
    (run : RunView) (decoded : R0P.Public M31Exact)
    (coins : GSConcreteByteDecoderBank.RawCoins) (w : Wspend)
    (hpublic : runDecodedPublic run = some decoded)
    (hresult : RawCutWordsFromRunExecutable.extractFromRun decoded run coins = some w) :
    runDecodedPublic run = some decoded ∧ Rspend decoded w := by
  exact ⟨hpublic, GSByteJointSpendExtractor.returned_valid decoded
    (RawCutWordsFromRunExecutable.initialWordsFromRun run)
    (fun _ => RawCutWordsFromRunExecutable.finalWordFromRun run) coins w hresult⟩

#print axioms runDecodedPublic
#print axioms extractFromRun_returned_valid
end AspisR1.RawCutWordsFromRunPublicValid
