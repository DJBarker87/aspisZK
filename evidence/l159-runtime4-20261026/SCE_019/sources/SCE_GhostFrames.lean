import SCE_ReplayTable
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_GhostFrames
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open CanonicalCutEnrichedTranscript RawCommitmentFrameReplay

/-- Ghost word installation changes neither frame bytes nor raw transcript
state transitions. These equalities are structural, including malformed rows. -/
theorem frameAt_enrich (w : Words) (pub : LiteralTranscript.Public)
    (s : State) (row : Nat) (m : LiteralTranscript.Message) :
    frameAt pub s row (enrichMessage w m) = frameAt pub s row m := by
  cases row <;> cases m <;> rfl

theorem successor_enrich (w : Words) (H : Bytes → State) (pub : LiteralTranscript.Public)
    (s : State) (row : Nat) (m : LiteralTranscript.Message) :
    successor H pub s row (enrichMessage w m) = successor H pub s row m := by
  cases row <;> cases m <;> rfl

theorem stateBefore_enrich (w : Words) (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : LiteralProtocol.Proof) (n : Nat) :
    stateBefore H pub (RawCutTranscriptRun.proof w pf) n = stateBefore H pub pf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stateBefore,RawCutTranscriptRun.proof,ih,successor_enrich]

theorem frame_enrich (w : Words) (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : LiteralProtocol.Proof) (row : Nat) :
    frame H pub (RawCutTranscriptRun.proof w pf) row = frame H pub pf row := by
  simp only [frame,stateBefore_enrich,RawCutTranscriptRun.proof,frameAt_enrich]

#print axioms frameAt_enrich
#print axioms successor_enrich
#print axioms stateBefore_enrich
#print axioms frame_enrich
end AspisR1.SCE_GhostFrames
end
