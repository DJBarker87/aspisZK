import BinFrameReplayWork
import BinEagerRecoveryWork

/-! Compose eager recovery with the complete last-write replay comparison
schedule. Query construction and continuation costs are still separate. -/
set_option autoImplicit false
namespace AspisR1.BinEagerFramedRecoveryWork
abbrev RunView := RawCutProverCompiler.RunView

def stage (run : RunView) : CanonicalCutEnrichedTranscript.Words × Nat :=
  let f0 := BinFrameReplayWork.frameWork run 0
  let f2 := BinFrameReplayWork.frameWork run 2
  let f30 := BinFrameReplayWork.frameWork run 30
  let r := BinEagerRecoveryWork.words run.1 f0.1 f2.1 f30.1
  (r.1, f0.2 + f2.2 + f30.2 + r.2)

attribute [local irreducible] BinEagerRecoveryWork.words

theorem stage_value (run : RunView) :
    (stage run).1 = (BinEagerRecoveryWork.stage run).1 := by
  simp only [stage, BinEagerRecoveryWork.stage, BinFrameReplayWork.frame_value,
    BinFrameReplayReads.frame_value]

theorem frame_length (run : RunView) (row : Nat) :
    (BinFrameReplayWork.frameWork run row).1.length ≤ 131072 := by
  rw [BinFrameReplayWork.frame_value, ← BinFrameReplayReads.frame_value]
  exact BinFrameSizeBound.counted_frame_length run row

theorem stage_work (run : RunView) :
    (stage run).2 ≤ 1000100000000 * (run.1.length + 1) := by
  have hf := BinFrameReplayWork.three_frames_work run
  have hr := BinEagerRecoveryWork.words_work run.1
    (BinFrameReplayWork.frameWork run 0).1
    (BinFrameReplayWork.frameWork run 2).1
    (BinFrameReplayWork.frameWork run 30).1
    (frame_length run 0) (frame_length run 2) (frame_length run 30)
  change _ + _ + _ + _ ≤ _
  omega

#print axioms stage_value
#print axioms frame_length
#print axioms stage_work
end AspisR1.BinEagerFramedRecoveryWork
