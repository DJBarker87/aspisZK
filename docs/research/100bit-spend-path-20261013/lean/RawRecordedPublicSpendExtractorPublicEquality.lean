import RawRecordedPublicSpendExtractorCore

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AspisR1.RawRecordedPublicSpendExtractor
open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.RawCutWordsFromRunPublicValid
open AspisR1.SpendRelation AspisV8R15.ExactTowerBase

attribute [local irreducible] RawCutWordsFromRunExecutable.extractFromRun
  GSByteJointSpendExtractor.extract RawCutWordsFromRunPublicValid.runDecodedPublic

private theorem bind_parse_eq {A B : Type} (parsed : Option A) (a : A)
    (f : A → Option B) (h : parsed = some a) : parsed.bind f = f a := by
  cases h
  rfl

/-- Only the Option parse result is transported; the concrete decoder
continuation and public parser stay opaque throughout elaboration. -/
theorem extract_eq_of_public_parse (run : RawCutProverCompiler.RunView)
    (decoded : R0P.Public M31Exact) (coins : GSConcreteByteDecoderBank.RawCoins)
    (hpublic : runDecodedPublic run = some decoded) :
    extract run coins = RawCutWordsFromRunExecutable.extractFromRun decoded run coins := by
  change (runDecodedPublic run).bind
      (fun p => RawCutWordsFromRunExecutable.extractFromRun p run coins) =
    RawCutWordsFromRunExecutable.extractFromRun decoded run coins
  exact @bind_parse_eq (R0P.Public M31Exact) Wspend
    (runDecodedPublic run) decoded
    (fun p => RawCutWordsFromRunExecutable.extractFromRun p run coins) hpublic

#print axioms extract_eq_of_public_parse
end AspisR1.RawRecordedPublicSpendExtractor
