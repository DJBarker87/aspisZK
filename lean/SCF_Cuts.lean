import SCE_ReplayWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCF_Cuts
open RawCutWordsFromRunExecutableBin

/-- Only the three replayed frames and the logs strictly before their first
reads enter recovery. This theorem permits arbitrary deletion after all cuts;
it does not assert that a physical account satisfies the cut equations. -/
theorem recovered (left right : RawCutProverCompiler.RunView)
    (frames : ∀ row, row = 0 ∨ row = 2 ∨ row = 30 →
      RawCommitmentFrameReplay.frameFromView left row =
        RawCommitmentFrameReplay.frameFromView right row)
    (cuts : ∀ row, row = 0 ∨ row = 2 ∨ row = 30 →
      BinRawByteCutRecovery.cut left.1 (RawCommitmentFrameReplay.frameFromView right row) =
        BinRawByteCutRecovery.cut right.1 (RawCommitmentFrameReplay.frameFromView right row)) :
    wordsFromRun left = wordsFromRun right := by
  unfold wordsFromRun
  rw [frames 0 (Or.inl rfl), frames 2 (Or.inr (Or.inl rfl)),
    frames 30 (Or.inr (Or.inr rfl))]
  rw [RawCutRecordedWordsExecutableBin.wordsFromRecordedCutsExec_eq_wordsFromRawCuts,
    RawCutRecordedWordsExecutableBin.wordsFromRecordedCutsExec_eq_wordsFromRawCuts]
  unfold BinCanonicalCutWords.wordsFromRawCuts BinCanonicalCutWords.rawC1Map
    BinCanonicalCutWords.rawC2Map BinCanonicalCutWords.rawFoldedMap
  rw [cuts 0 (Or.inl rfl), cuts 2 (Or.inr (Or.inl rfl)), cuts 30 (Or.inr (Or.inr rfl))]

#print axioms recovered
end AspisR1.SCF_Cuts
end
