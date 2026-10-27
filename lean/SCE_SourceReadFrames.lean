import SCE_SourceFirst
import SCE_ModelReadFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SourceReadFrames
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin

theorem frames {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (raw : AcceptedVerifierJoin c D rust) (P : ByteProver) (H : Bytes → State)
    (accepted : (eval H (originalWith rust (F3T_Canon.canon (lift c P)))).2.2 = true) :
    let v := view (eval H (originalWith rust (F3T_Canon.canon (lift c P))))
    Read v.1 (RawCommitmentFrameReplay.frameFromView v 0) ∧
    Read v.1 (RawCommitmentFrameReplay.frameFromView v 2) ∧
    Read v.1 (RawCommitmentFrameReplay.frameFromView v 30) := by
  have same := SCE_SourceFirst.original c D rust physical raw P H accepted
  rw [same] at accepted ⊢
  exact SCE_ModelReadFrames.frames D (lift c P) H accepted

#print axioms frames
end AspisR1.SCE_SourceReadFrames
end
