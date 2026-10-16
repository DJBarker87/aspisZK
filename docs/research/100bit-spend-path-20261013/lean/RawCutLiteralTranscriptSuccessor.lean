import R1LiteralByteProtocol
import RawCutLiteralStateSuccessor
import R1LiteralRun

/-! Connect the literal-byte protocol transcript to the typed-address literal
run, then expose the exact state emitted by one protocol sampler call. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutLiteralTranscriptSuccessor

open FS FS2
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.LiteralTranscript

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := LiteralByteProtocol.State

private theorem protocol_transcript_eq
    (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : LiteralProtocol.Proof) (n : Nat) :
    (LiteralByteProtocol.protocol decoder).transcript H pub pf n =
      LiteralRun.transcript (fun a => H a.toBytes) pub pf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).ext
        (pf n)
        (eval H (LiteralByteSampler.samp n
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)
          (pf n)).toProgram).2 = _
      rw [ih, LiteralByteSampler.eval_eq]
      rfl

theorem actual_successor_state
    (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : LiteralProtocol.Proof) (i : Nat) :
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf (i + 1))) =
      (eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf i).toProgram).2.2 := by
  rw [protocol_transcript_eq]
  change UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix
        (LiteralRun.transcript (fun a => H a.toBytes) pub pf (i + 1))) = _
  rw [LiteralRun.transcript, LiteralTranscript.erasePrefix_ext,
    UnifiedSampler.stateOf_ext]
  have hchain : (LiteralByteProtocol.protocol decoder).chain H pub pf i =
      LiteralByteSampler.samp i
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf i) (pf i) := rfl
  rw [hchain]
  rw [LiteralByteSampler.eval_eq]
  rw [protocol_transcript_eq decoder H pub pf i]
  rfl

#print axioms actual_successor_state

end AspisR1.RawCutLiteralTranscriptSuccessor
end
