import SCE_ReplayTable
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_ReplayMaps
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem words_at_read_cuts (prior suffix : List (Bytes × State))
    (f0 f2 f30 : Bytes) (r0 r2 r30 : State)
    (h0 : Read prior f0) (h2 : Read prior f2) (h30 : Read prior f30) :
    BinCanonicalCutWords.wordsFromRawCuts (prior ++ suffix) f0 f2 f30 r0 r2 r30 =
      BinCanonicalCutWords.wordsFromRawCuts prior f0 f2 f30 r0 r2 r30 := by
  unfold BinCanonicalCutWords.wordsFromRawCuts BinCanonicalCutWords.rawC1Map
    BinCanonicalCutWords.rawC2Map BinCanonicalCutWords.rawFoldedMap
  rw [SCE_ReplayTable.cut_append prior suffix f0 h0,
    SCE_ReplayTable.cut_append prior suffix f2 h2,
    SCE_ReplayTable.cut_append prior suffix f30 h30]

#print axioms words_at_read_cuts
end AspisR1.SCE_ReplayMaps
end
