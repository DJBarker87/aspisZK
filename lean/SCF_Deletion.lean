import SCF_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCF_Deletion
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open RawCutWordsFromRunExecutableBin

/-- A deletion strictly after a shared first-read prior preserves all three
recovery tables. The frame-identification obligation is explicit and separate
from read-budget/acceptance facts. -/
theorem recovered (left right : RawCutProverCompiler.RunView)
    (prior extra suffix : List (Bytes × State))
    (left_log : left.1 = prior ++ (extra ++ suffix))
    (right_log : right.1 = prior ++ suffix)
    (frames : ∀ row, row = 0 ∨ row = 2 ∨ row = 30 →
      RawCommitmentFrameReplay.frameFromView left row =
        RawCommitmentFrameReplay.frameFromView right row)
    (read_prior : ∀ row, row = 0 ∨ row = 2 ∨ row = 30 →
      Read prior (RawCommitmentFrameReplay.frameFromView right row)) :
    wordsFromRun left = wordsFromRun right := by
  apply SCF_Cuts.recovered left right frames
  intro row selected
  rw [left_log, right_log,
    SCE_ReplayTable.cut_append prior (extra ++ suffix) _ (read_prior row selected),
    SCE_ReplayTable.cut_append prior suffix _ (read_prior row selected)]

#print axioms recovered
end AspisR1.SCF_Deletion
end
