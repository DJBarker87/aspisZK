import RPz8_ARQ_FrameAgreement
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_FrameReads
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem in_sampler (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (valid : ∀ j, j ≤ 30 → LiteralTranscript.valid j (pf j)) :
    ∀ row, row = 0 ∨ row = 2 ∨ row = 30 →
    FS2.Duplex.Read (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) pub pf)).1
      (RawCommitmentFrameReplay.frame H pub pf row) := by
  have frames := RawCommitmentFrameReplayCorrect.commitment_frames_eq D H pub pf valid
  intro row selected
  have small : row < 33 := by rcases selected with rfl | rfl | rfl <;> omega
  have read := OraclePortReplay.frame_in_sampler D H pub pf row small
  rcases selected with rfl | rfl | rfl
  · rwa [←frames.1] at read
  · rwa [←frames.2.1] at read
  · rwa [←frames.2.2] at read

#print axioms in_sampler
end AspisR1.ARQ_FrameReads
end
