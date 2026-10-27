import SCF_FrameReplay
import ARQ_CommonCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_FrameAgreement
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem frames (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (left right : RawCutProverCompiler.RunView)
    (pub : left.2.1.1 = right.2.1.1) (proof : left.2.1.2 = right.2.1.2)
    (consistentL : ∀ q ∈ left.1, q.2 = H q.1)
    (consistentR : ∀ q ∈ right.1, q.2 = H q.1)
    (readsL : ∀ a, FS2.Duplex.Read
      (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) right.2.1.1 right.2.1.2)).1 a →
      FS2.Duplex.Read left.1 a)
    (readsR : ∀ a, FS2.Duplex.Read
      (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) right.2.1.1 right.2.1.2)).1 a →
      FS2.Duplex.Read right.1 a)
    (valid : ∀ j, j < 30 → LiteralTranscript.valid j (right.2.1.2 j)) :
    ∀ row, row = 0 ∨ row = 2 ∨ row = 30 →
      RawCommitmentFrameReplay.frameFromView left row = RawCommitmentFrameReplay.frameFromView right row := by
  intro row selected
  have bound : row ≤ 30 := by rcases selected with rfl | rfl | rfl <;> omega
  have rowValid : ∀ j, j < row → LiteralTranscript.valid j (right.2.1.2 j) :=
    fun j h => valid j (by omega)
  unfold RawCommitmentFrameReplay.frameFromView
  rw [pub,proof]
  rw [SCF_FrameReplay.recorded D H left.1 right.2.1.1 right.2.1.2 consistentL readsL row (by omega) rowValid,
    SCF_FrameReplay.recorded D H right.1 right.2.1.1 right.2.1.2 consistentR readsR row (by omega) rowValid]

#print axioms frames
end AspisR1.ARQ_FrameAgreement
end
