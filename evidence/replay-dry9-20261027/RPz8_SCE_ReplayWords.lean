import RPz8_SCE_ReplayFrames
import RPz8_SCE_ReplayMaps
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_ReplayWords
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open CanonicalCutEnrichedTranscript SCE_ReplayFrames RawCutWordsFromRunExecutableBin

/-- Literal log equality is unnecessary for extractor-word transport. Known
replay and ghost enrichment preserve the executable recovery at read cuts. -/
theorem recovered (run : RawCutProverCompiler.RunView) (suffix : List (Bytes × State))
    (w : CanonicalCutEnrichedTranscript.Words) (H : Bytes → State)
    (consistent : ∀ q ∈ run.1 ++ suffix, q.2 = H q.1)
    (known : ∀ a ∈ suffix.map Prod.fst, a ∈ run.1.map Prod.fst)
    (h0 : Read run.1 (RawCommitmentFrameReplay.frameFromView run 0))
    (h2 : Read run.1 (RawCommitmentFrameReplay.frameFromView run 2))
    (h30 : Read run.1 (RawCommitmentFrameReplay.frameFromView run 30)) :
    wordsFromRun (annotated run suffix w) = wordsFromRun run := by
  unfold wordsFromRun
  rw [frame_same run suffix w H consistent known 0,
    frame_same run suffix w H consistent known 2,
    frame_same run suffix w H consistent known 30]
  change RawCutRecordedWordsExecutableBin.wordsFromRecordedCutsExec (run.1 ++ suffix) _ _ _ _ _ _ = _
  rw [RawCutRecordedWordsExecutableBin.wordsFromRecordedCutsExec_eq_wordsFromRawCuts,
    RawCutRecordedWordsExecutableBin.wordsFromRecordedCutsExec_eq_wordsFromRawCuts]
  exact SCE_ReplayMaps.words_at_read_cuts run.1 suffix _ _ _ _ _ _ h0 h2 h30

#print axioms recovered
end AspisR1.SCE_ReplayWords
end
