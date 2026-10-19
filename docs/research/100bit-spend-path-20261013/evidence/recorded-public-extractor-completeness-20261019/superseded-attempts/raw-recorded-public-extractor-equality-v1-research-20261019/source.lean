import RawRecordedPublicSpendExtractorCore

set_option autoImplicit false
namespace AspisR1.RawRecordedPublicSpendExtractor
open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.RawCutWordsFromRunPublicValid
open AspisR1.SpendRelation AspisV8R15.ExactTowerBase

attribute [local irreducible] RawCutWordsFromRunPublicValid.runDecodedPublic
  RawCutWordsFromRunExecutable.extractFromRun GSByteJointSpendExtractor.extract
  SemanticPublicWire.parsePublic

theorem extract_eq_of_public_parse (run : RawCutProverCompiler.RunView)
    (decoded : R0P.Public M31Exact) (coins : GSConcreteByteDecoderBank.RawCoins)
    (hpublic : runDecodedPublic run = some decoded) :
    extract run coins = RawCutWordsFromRunExecutable.extractFromRun decoded run coins := by
  unfold AspisR1.RawRecordedPublicSpendExtractor.extract
  rw [hpublic]
  rfl

/-- Every returned witness satisfies the maintained spend relation for the
public bytes of this same recorded run, including AppendBinding. -/
#check extract_eq_of_public_parse
#print axioms extract_eq_of_public_parse

#print axioms extract_eq_of_public_parse
end AspisR1.RawRecordedPublicSpendExtractor
