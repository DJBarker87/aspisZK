import RPz8_SCE_GhostFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_ReplayFrames
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open CanonicalCutEnrichedTranscript

def annotated (run : RawCutProverCompiler.RunView) (suffix : List (Bytes × State))
    (w : Words) : RawCutProverCompiler.RunView :=
  (run.1 ++ suffix,((run.2.1.1,RawCutTranscriptRun.proof w run.2.1.2),run.2.2))

theorem frame_same (run : RawCutProverCompiler.RunView) (suffix : List (Bytes × State))
    (w : Words) (H : Bytes → State)
    (consistent : ∀ q ∈ run.1 ++ suffix, q.2 = H q.1)
    (known : ∀ a ∈ suffix.map Prod.fst, a ∈ run.1.map Prod.fst) (row : Nat) :
    RawCommitmentFrameReplay.frameFromView (annotated run suffix w) row =
      RawCommitmentFrameReplay.frameFromView run row := by
  unfold RawCommitmentFrameReplay.frameFromView annotated
  dsimp only
  rw [SCE_ReplayTable.oracle_known_suffix H run.1 suffix consistent known,
    SCE_GhostFrames.frame_enrich]

#print axioms frame_same
end AspisR1.SCE_ReplayFrames
end
