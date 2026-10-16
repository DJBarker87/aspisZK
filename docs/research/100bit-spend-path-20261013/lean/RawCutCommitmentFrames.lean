import RawCutWordsFromView
import R1OpeningRecordCodec

/-! The three actual literal-sampler first cells contain precisely the roots
parsed by the existing strict record codecs. This discharges the raw target
parser obligations from well-formed commitment messages. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutCommitmentFrames

open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open LiteralTranscript RawByteCollisionTargets

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (label : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
  cases s <;> rfl

def state (P : LiteralTranscript.Prefix) : State :=
  UnifiedSampler.stateOf SelectedTranscriptParams.params (erasePrefix P)

def input (P : LiteralTranscript.Prefix) (i : Nat)
    (m : LiteralTranscript.BytesMessage) : Bytes :=
  bytes (state P) ++ [0, SelectedTranscriptParams.label i] ++ m.val

theorem first_initial (P : LiteralTranscript.Prefix) (root : State) (w : C1Word) :
    firstCell (LiteralByteSampler.samp 0 P (.initial root w)) =
      some (PublicInitFrame.frame P.statement.pubBytes root) := by
  unfold LiteralByteSampler.samp
  rw [firstCell_map]
  change (some (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits root)).map
    Addr.toBytes = _
  simp only [Option.map_some, PublicInitFrame.addr, Addr.toBytes_ofBytes]

theorem first_c2 (P : LiteralTranscript.Prefix) (m : LiteralTranscript.BytesMessage)
    (w : C2Word) : firstCell (LiteralByteSampler.samp 2 P (.c2 m w)) = some (input P 2 m) := by
  unfold LiteralByteSampler.samp
  rw [firstCell_map]
  change (some (UnifiedSampler.absorb SelectedTranscriptParams.params 2 (erasePrefix P) m)).map
    Addr.toBytes = _
  simp only [Option.map_some, UnifiedSampler.absorb, absorbA, Addr.toBytes_ofBytes]
  rfl

theorem first_second (P : LiteralTranscript.Prefix) (m : LiteralTranscript.BytesMessage)
    (w : VWord) : firstCell (LiteralByteSampler.samp 30 P (.second m w)) = some (input P 30 m) := by
  unfold LiteralByteSampler.samp
  rw [firstCell_map]
  change (some (UnifiedSampler.absorb SelectedTranscriptParams.params 30 (erasePrefix P) m)).map
    Addr.toBytes = _
  simp only [Option.map_some, UnifiedSampler.absorb, absorbA, Addr.toBytes_ofBytes]
  rfl

theorem initial_root (P : LiteralTranscript.Prefix) (root : State) (w : C1Word) :
    (firstCell (LiteralByteSampler.samp 0 P (.initial root w))).bind
      (RawByteCollisionTargets.pred 8) = some root := by
  rw [first_initial]
  exact RawByteCollisionTargets.trailing_frame (PublicInitFrame.pre P.statement.pubBytes) root

theorem c2_input (P : LiteralTranscript.Prefix) (m : LiteralTranscript.BytesMessage)
    (root : State)
    (h : SemanticRecordCodec.decode ⟨2, by decide⟩ m.val =
      some ⟨.c2Root root, by rfl⟩) :
    input P 2 m = CommitmentRootFrames.c2Frame (state P) root := by
  have hm := SemanticRecordCodec.encode_of_decode ⟨2, by decide⟩ m.val
    ⟨.c2Root root, by rfl⟩ h
  unfold input
  rw [← hm]
  simp only [SemanticRecordCodec.encode, SemanticRecordCodec.payloadTag,
    SemanticRecordCodec.payloadBytes, RecordFrameCodec.frame, RecordFrameCodec.header,
    bytes_length]
  change bytes (state P) ++ [0, 162] ++ ([1] ++ [32, 0, 0, 0] ++ bytes root) = _
  simp only [CommitmentRootFrames.c2Frame, CommitmentRootFrames.c2Prefix, List.append_assoc]
  rfl

theorem c2_root (P : LiteralTranscript.Prefix) (m : LiteralTranscript.BytesMessage)
    (w : C2Word) (root : State)
    (h : SemanticRecordCodec.decode ⟨2, by decide⟩ m.val =
      some ⟨.c2Root root, by rfl⟩) :
    (firstCell (LiteralByteSampler.samp 2 P (.c2 m w))).bind
      (RawByteCollisionTargets.pred 8) = some root := by
  rw [first_c2, Option.bind_some, c2_input P m root h]
  exact RawByteCollisionTargets.trailing_frame (CommitmentRootFrames.c2Prefix (state P)) root

theorem second_input (P : LiteralTranscript.Prefix) (m : LiteralTranscript.BytesMessage)
    (payload : OpeningRecordCodec.Payload .second)
    (h : OpeningRecordCodec.decode .second m.val = some payload) :
    input P 30 m = CommitmentRootFrames.foldedFrame (state P) payload.1
      (SelectedFieldSequenceCodec.encodeWide payload.2) := by
  have hm := OpeningRecordCodec.encode_of_decode m.val payload h
  unfold input
  rw [← hm]
  unfold OpeningRecordCodec.encode LengthFrameCodec.frame
  rw [OpeningRecordCodec.encodePayload_length]
  change bytes (state P) ++ [0, 190] ++
    ([0, 1, 0, 0] ++ (bytes payload.1 ++ SelectedFieldSequenceCodec.encodeWide payload.2)) = _
  simp only [CommitmentRootFrames.foldedFrame, CommitmentRootFrames.foldedPrefix, List.append_assoc]
  rfl

theorem second_root (P : LiteralTranscript.Prefix) (m : LiteralTranscript.BytesMessage)
    (w : VWord) (payload : OpeningRecordCodec.Payload .second)
    (h : OpeningRecordCodec.decode .second m.val = some payload) :
    (firstCell (LiteralByteSampler.samp 30 P (.second m w))).bind
      (RawByteCollisionTargets.pred 9) = some payload.1 := by
  rw [first_second, Option.bind_some, second_input P m payload h]
  exact RawByteCollisionTargets.fixed_frame 38 (CommitmentRootFrames.foldedPrefix (state P))
    payload.1 (SelectedFieldSequenceCodec.encodeWide payload.2)
    (CommitmentRootFrames.foldedPrefix_length (state P))

#print axioms first_initial
#print axioms first_c2
#print axioms first_second
#print axioms initial_root
#print axioms c2_root
#print axioms second_root
end AspisR1.RawCutCommitmentFrames
end
