import SCE_Annotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_ReplayExtractTransport
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
open SCE_ReplayFrames RawCutWordsFromRunExecutableBin
/-- Equality for EACH private coin tape, stronger than only equal mean mass. -/
theorem extract (run : RawCutProverCompiler.RunView) (suffix : List (Bytes × State))
    (w : CanonicalCutEnrichedTranscript.Words) (H : Bytes → State)
    (consistent : ∀ q ∈ run.1 ++ suffix, q.2 = H q.1)
    (known : ∀ a ∈ suffix.map Prod.fst, a ∈ run.1.map Prod.fst)
    (h0 : Read run.1 (RawCommitmentFrameReplay.frameFromView run 0))
    (h2 : Read run.1 (RawCommitmentFrameReplay.frameFromView run 2))
    (h30 : Read run.1 (RawCommitmentFrameReplay.frameFromView run 30))
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    RawRecordedPublicSpendExtractorBin.extract run coins =
      RawRecordedPublicSpendExtractorBin.extract (annotated run suffix w) coins := by
  exact SCE_ReplayExtractor.extract_congr _ _ rfl
    (SCE_ReplayWords.recovered run suffix w H consistent known h0 h2 h30).symm coins
#print axioms extract
end AspisR1.SCE_ReplayExtractTransport
end
