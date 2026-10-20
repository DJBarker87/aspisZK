import RawCutWordsFromRunPublicValidBin

/-! An ordinary recorded-run extractor including public-statement decoding.
Only the recorded view and private finite byte tape are inputs; no external
oracle or separately supplied decoded public is needed. Completeness still
requires accepted-model/source conditions. -/
set_option autoImplicit false
namespace AspisR1.RawRecordedPublicSpendExtractorBin
open AspisR1.RawCutWordsFromRunExecutableBin
open AspisR1.RawCutWordsFromRunPublicValidBin
open AspisR1.SpendRelation AspisV8R15.ExactTowerBase

/-- Parse the public from this run, reconstruct its commitment words, and run
the actual finite-byte decoder/list/checked-witness pipeline. -/
def extract (run : RawCutProverCompiler.RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) : Option Wspend :=
  (runDecodedPublic run).bind fun decoded =>
    RawCutWordsFromRunExecutableBin.extractFromRun decoded run coins

#check extract
#print axioms extract
end AspisR1.RawRecordedPublicSpendExtractorBin
