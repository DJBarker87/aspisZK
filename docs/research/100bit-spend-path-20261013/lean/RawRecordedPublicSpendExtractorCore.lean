import RawCutWordsFromRunPublicValid

/-! An ordinary recorded-run extractor including public-statement decoding.
Only the recorded view and private finite byte tape are inputs; no external
oracle or separately supplied decoded public is needed. Completeness still
requires accepted-model/source conditions. -/
set_option autoImplicit false
namespace AspisR1.RawRecordedPublicSpendExtractor
open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.RawCutWordsFromRunPublicValid
open AspisR1.SpendRelation AspisV8R15.ExactTowerBase

/-- Parse the public from this run, reconstruct its commitment words, and run
the actual finite-byte decoder/list/checked-witness pipeline. -/
def extract (run : RawCutProverCompiler.RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) : Option Wspend :=
  (runDecodedPublic run).bind fun decoded =>
    RawCutWordsFromRunExecutable.extractFromRun decoded run coins

#check extract
#print axioms extract
end AspisR1.RawRecordedPublicSpendExtractor
