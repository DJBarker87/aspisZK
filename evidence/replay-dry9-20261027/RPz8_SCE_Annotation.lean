import RPz8_SCE_ReplayExtractor
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_Annotation
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open CanonicalCutEnrichedTranscript SCE_ReplayFrames RawCutWordsFromRunExecutableBin

/-- Transport through known-cell replay and ghost metadata, retaining the
physical log on the left. No literal replay-log equality is assumed. -/
theorem transport (run : RawCutProverCompiler.RunView) (suffix : List (Bytes × State))
    (w : CanonicalCutEnrichedTranscript.Words) (H : Bytes → State)
    (consistent : ∀ q ∈ run.1 ++ suffix, q.2 = H q.1)
    (known : ∀ a ∈ suffix.map Prod.fst, a ∈ run.1.map Prod.fst)
    (h0 : Read run.1 (RawCommitmentFrameReplay.frameFromView run 0))
    (h2 : Read run.1 (RawCommitmentFrameReplay.frameFromView run 2))
    (h30 : Read run.1 (RawCommitmentFrameReplay.frameFromView run 30)) :
    RawRecordedOracleExtractionMassBin.failureMass run =
      RawRecordedOracleExtractionMassBin.failureMass (annotated run suffix w) := by
  apply SCE_ReplayExtractor.mass_congr
  · rfl
  · exact (SCE_ReplayWords.recovered run suffix w H consistent known h0 h2 h30).symm
  · rfl

#print axioms transport
end AspisR1.SCE_Annotation
end
