import RawRecordedPublicSpendExtractorCore

set_option autoImplicit false
namespace AspisR1.RawRecordedPublicSpendExtractor
open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.RawCutWordsFromRunPublicValid
open AspisR1.SpendRelation AspisV8R15.ExactTowerBase

attribute [local irreducible] RawCutWordsFromRunExecutable.extractFromRun
  GSByteJointSpendExtractor.extract
attribute [local reducible] AspisR1.RawRecordedPublicSpendExtractor.extract

/-- Transport only the small Option result; do not rewrite or normalize the
large concrete decoder continuation. -/
theorem extract_eq_of_public_parse (run : RawCutProverCompiler.RunView)
    (decoded : R0P.Public M31Exact) (coins : GSConcreteByteDecoderBank.RawCoins)
    (hpublic : runDecodedPublic run = some decoded) :
    extract run coins = RawCutWordsFromRunExecutable.extractFromRun decoded run coins :=
  congrArg (fun parsed : Option (R0P.Public M31Exact) => parsed.bind
    (fun p => RawCutWordsFromRunExecutable.extractFromRun p run coins)) hpublic

#print axioms extract_eq_of_public_parse
end AspisR1.RawRecordedPublicSpendExtractor
