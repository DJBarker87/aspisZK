import SCF_Cuts
import OraclePortReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCF_FrameReplay
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Fresh outer addresses are harmless to replay whenever the SAME sampler
reads remain in the recording. Unlike known-suffix replay, this does not
require the additional addresses to occur in the source log. -/
theorem recorded (D : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (tr : List (Bytes × State))
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (consistent : ∀ q ∈ tr, q.2 = H q.1)
    (reads : ∀ a, FS2.Duplex.Read
      (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) pub pf)).1 a →
      FS2.Duplex.Read tr a)
    (row : Nat) (small : row ≤ 31)
    (valid : ∀ j, j < row → LiteralTranscript.valid j (pf j)) :
    RawCommitmentFrameReplay.frame (OracleProgramReplay.oracleOf tr) pub pf row =
      RawCommitmentFrameReplay.frame H pub pf row := by
  have transcript : (LiteralByteProtocol.protocol D).transcript
      (OracleProgramReplay.oracleOf tr) pub pf row =
      (LiteralByteProtocol.protocol D).transcript H pub pf row := by
    apply OracleProgramReplay.transcript_eq_of_agrees
      (LiteralByteProtocol.protocol D) (RawCutTranscriptRun.decisionOnBytes (fun _ _ => false)) H
    · intro a member
      exact OracleProgramReplay.oracleOf_eq H tr consistent a (reads a member)
    · change row ≤ 33
      omega
  unfold RawCommitmentFrameReplay.frame
  rw [RawCommitmentFrameReplayCorrect.stateBefore_eq D _ pub pf row small valid,
    RawCommitmentFrameReplayCorrect.stateBefore_eq D H pub pf row small valid,
    transcript]

#print axioms recorded
end AspisR1.SCF_FrameReplay
end
