import SCE_ReplayWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_RecoveredExtraction
open RawCutWordsFromRunExecutableBin

theorem extracted (left right : RawCutProverCompiler.RunView)
    (words : wordsFromRun left = wordsFromRun right)
    (pub : R0P.Public AspisV8R15.ExactTowerBase.M31Exact)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    extractFromRun pub left coins = extractFromRun pub right coins := by
  have initial : initialWordsFromRun left = initialWordsFromRun right := by
    unfold initialWordsFromRun
    rw [words]
  have final : finalWordFromRun left = finalWordFromRun right :=
    congrArg CanonicalCutEnrichedTranscript.Words.final words
  exact congrArg₂ (fun i f => GSByteJointSpendExtractor.extract pub i (fun _ => f) coins) initial final

#print axioms extracted
end AspisR1.SCE_RecoveredExtraction
end
