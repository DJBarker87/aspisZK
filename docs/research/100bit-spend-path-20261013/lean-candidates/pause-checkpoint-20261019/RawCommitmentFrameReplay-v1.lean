import RawTranscriptFrameBytes
import RawCutWordsFromView
import RawCutLiteralStateSuccessor
import RawCutLiteralTranscriptSuccessor

/-! Executable state-only replay for the three commitment cuts. The last cut
is before row 30, so no query-row scanner or field challenge decoder is needed.
Equivalence with the semantic transcript is a separate theorem below/in progress. -/
set_option autoImplicit false
namespace AspisR1.RawCommitmentFrameReplay
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

abbrev Public := LiteralTranscript.Public
abbrev Message := LiteralTranscript.Message
abbrev Proof := LiteralProtocol.Proof

def zeroState : State := fun _ => 0

def frameAt (pub : Public) (state : State) (row : Nat) (m : Message) : Bytes :=
  match row, m with
  | 0, .initial root _ => RawTranscriptFrameBytes.publicInit pub.pubBytes root
  | 0, _ => bytes zeroState ++ [1]
  | _ + 1, .initial _ _ => bytes zeroState ++ [1]
  | _ + 1, .payload payload => RawTranscriptFrameBytes.absorb state row payload.val
  | _ + 1, .c2 payload _ => RawTranscriptFrameBytes.absorb state row payload.val
  | _ + 1, .second payload _ => RawTranscriptFrameBytes.absorb state row payload.val

def payloadSuccessor (H : Bytes → State) (pub : Public)
    (state : State) (row : Nat) (payload : Bytes) : State :=
  let absorbed := H (RawTranscriptFrameBytes.absorb state row payload)
  let advanced := H (RawTranscriptFrameBytes.advance absorbed)
  if row = 26 then H (RawTranscriptFrameBytes.reseed pub.tag advanced) else advanced

/-- For rows below 31 this is exactly the state component of a sampler call.
The query row is deliberately outside the equivalence domain. -/
def successor (H : Bytes → State) (pub : Public)
    (state : State) (row : Nat) (m : Message) : State :=
  match row, m with
  | 0, .initial root _ =>
      let initialized := H (RawTranscriptFrameBytes.publicInit pub.pubBytes root)
      let absorbed := H (RawTranscriptFrameBytes.rowZero initialized)
      H (RawTranscriptFrameBytes.advance absorbed)
  | 0, _ => zeroState
  | _ + 1, .initial _ _ => zeroState
  | _ + 1, .payload payload => payloadSuccessor H pub state row payload.val
  | _ + 1, .c2 payload _ => payloadSuccessor H pub state row payload.val
  | _ + 1, .second payload _ => payloadSuccessor H pub state row payload.val

def stateBefore (H : Bytes → State) (pub : Public) (pf : Proof) : Nat → State
  | 0 => zeroState
  | n + 1 => successor H pub (stateBefore H pub pf n) n (pf n)

def frame (H : Bytes → State) (pub : Public) (pf : Proof) (row : Nat) : Bytes :=
  frameAt pub (stateBefore H pub pf row) row (pf row)

def frameFromView (run : RawCutProverCompiler.RunView) (row : Nat) : Bytes :=
  frame (OracleProgramReplay.oracleOf run.1) run.2.1.1 run.2.1.2 row

theorem initial_frame (H : Bytes → State) (pub : Public) (pf : Proof)
    (root : State) (word : LiteralTranscript.C1Word)
    (hm : pf 0 = .initial root word) :
    frame H pub pf 0 = (PublicInitFrame.addr pub.pubBytes pub.initFits root).toBytes := by
  simp only [frame, frameAt, hm]
  exact RawTranscriptFrameBytes.publicInit_eq pub.pubBytes pub.initFits root

#print axioms frameAt
#print axioms successor
#print axioms stateBefore
#print axioms frameFromView
#print axioms initial_frame
end AspisR1.RawCommitmentFrameReplay
