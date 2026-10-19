import RawRecordedPublicSpendExtractorPublicEquality

/-! Every successful output of the ordinary recorded-public extractor
satisfies the public byte relation, with no terminal-check premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AspisR1.RawRecordedPublicSpendExtractor
open AspisR1.RawCutWordsFromRunPublicValid
open AspisR1.SpendRelation AspisV8R15.ExactTowerBase

attribute [local irreducible] RawCutWordsFromRunExecutable.extractFromRun
  GSByteJointSpendExtractor.extract runDecodedPublic

/-- The parser is that of this exact recorded run; successful extraction
therefore gives a witness for the recorded public bytes. -/
theorem returned_relation (run : RawCutProverCompiler.RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) (w : Wspend)
    (h : extract run coins = some w) :
    LiteralProtocol.relation run.2.1.1 w := by
  change (runDecodedPublic run).bind
    (fun p => RawCutWordsFromRunExecutable.extractFromRun p run coins) = some w at h
  obtain ⟨decoded, hpublic, hresult⟩ := Option.bind_eq_some_iff.mp h
  have hrel := RawCutWordsFromRunPublicValid.extractFromRun_returned_valid
    run decoded coins w hpublic hresult
  refine ⟨decoded, ?_, hrel.2⟩
  unfold RawCutWordsFromRunPublicValid.runDecodedPublic at hpublic
  exact hpublic

#print axioms returned_relation
end AspisR1.RawRecordedPublicSpendExtractor
