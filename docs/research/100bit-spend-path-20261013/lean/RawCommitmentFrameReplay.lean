import RawTranscriptFrameBytes
import RawCutWordsFromView
import RawCutLiteralStateSuccessor
import RawCutLiteralTranscriptSuccessor

/-! Executable state-only replay for the three commitment cuts. The last cut
is before row 30, so no query-row scanner or field challenge decoder is needed.
Equivalence with the semantic transcript is a separate theorem below/in progress. -/
set_option autoImplicit false
namespace AspisR1.RawCommitmentFrameReplay
open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
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

/-- A payload row only needs the previous raw state. Challenge values do
not enter its successor-state computation. -/
theorem payloadSuccessor_eq_sampler
    (H : Bytes → State) (pub : Public) (P : LiteralTranscript.Prefix)
    (hpub : P.statement = pub) (row : Nat)
    (hrow0 : row ≠ 0) (hrow31 : row ≠ 31)
    (payload : SelectedTranscriptParams.Message) :
    payloadSuccessor H pub
        (UnifiedSampler.stateOf SelectedTranscriptParams.params
          (LiteralTranscript.erasePrefix P)) row payload.val =
      (eval H (LiteralByteSampler.samp row P (.payload payload)).toProgram).2.2 := by
  have ha : RawTranscriptFrameBytes.absorb
      (UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix P)) row payload.val =
      (UnifiedSampler.absorb SelectedTranscriptParams.params row
        (LiteralTranscript.erasePrefix P) payload).toBytes :=
    RawTranscriptFrameBytes.absorb_eq _ row payload
  dsimp only [payloadSuccessor]
  rw [ha, RawTranscriptFrameBytes.advance_eq SelectedTranscriptParams.params]
  by_cases h26 : row = 26
  · subst row
    simp only [↓reduceIte]
    rw [RawTranscriptFrameBytes.reseed_eq pub.tag
      (show 62 ≤ SelectedTranscriptParams.L by norm_num [SelectedTranscriptParams.L])]
    have hs := RawCutLiteralStateSuccessor.reseed_payload_state H P payload
    convert hs.symm using 1 <;>
      simp only [LiteralTranscript.erasePrefix, hpub] <;> rfl
  · rw [if_neg h26]
    exact (RawCutLiteralStateSuccessor.ordinary_payload_state
      H P payload row hrow0 h26 hrow31).symm

/-- Exact pointwise compatibility for valid rows before the query scanner.
The supplied raw state is the state stored by this same semantic prefix. -/
theorem successor_eq_sampler
    (H : Bytes → State) (pub : Public) (P : LiteralTranscript.Prefix)
    (hpub : P.statement = pub) (row : Nat) (hrow : row < 31)
    (m : Message) (hm : LiteralTranscript.valid row m) :
    successor H pub
        (UnifiedSampler.stateOf SelectedTranscriptParams.params
          (LiteralTranscript.erasePrefix P)) row m =
      (eval H (LiteralByteSampler.samp row P m).toProgram).2.2 := by
  cases row with
  | zero =>
    cases m with
    | initial root word =>
      rw [RawCutLiteralStateSuccessor.initial_state H P root word]
      simp only [successor]
      rw [RawTranscriptFrameBytes.publicInit_eq pub.pubBytes pub.initFits root]
      rw [RawTranscriptFrameBytes.rowZero_eq SelectedTranscriptParams.params
        (show 5 ≤ SelectedTranscriptParams.params.D by
          norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])]
      rw [RawTranscriptFrameBytes.advance_eq SelectedTranscriptParams.params]
      rw [hpub]
      rfl
    | payload payload => simp [LiteralTranscript.valid] at hm
    | c2 payload word => simp [LiteralTranscript.valid] at hm
    | second payload word => simp [LiteralTranscript.valid] at hm
  | succ row =>
    have h0 : row + 1 ≠ 0 := by omega
    have h31 : row + 1 ≠ 31 := by omega
    cases m with
    | initial root word => simp [LiteralTranscript.valid] at hm
    | payload payload =>
      exact payloadSuccessor_eq_sampler H pub P hpub (row + 1) h0 h31 payload
    | c2 payload word =>
      change payloadSuccessor H pub _ (row + 1) payload.val =
        (eval H (LiteralByteSampler.samp (row + 1) P (.payload payload)).toProgram).2.2
      exact payloadSuccessor_eq_sampler H pub P hpub (row + 1) h0 h31 payload
    | second payload word =>
      change payloadSuccessor H pub _ (row + 1) payload.val =
        (eval H (LiteralByteSampler.samp (row + 1) P (.payload payload)).toProgram).2.2
      exact payloadSuccessor_eq_sampler H pub P hpub (row + 1) h0 h31 payload

#print axioms frameAt
#print axioms successor
#print axioms stateBefore
#print axioms frameFromView
#print axioms initial_frame
#print axioms payloadSuccessor_eq_sampler
#print axioms successor_eq_sampler
end AspisR1.RawCommitmentFrameReplay
