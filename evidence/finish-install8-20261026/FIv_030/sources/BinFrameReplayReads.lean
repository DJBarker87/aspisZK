import RawCommitmentFrameReplay

/-! Address-specific last-write replay, preserving duplicate-write semantics.
Every log entry is inspected on every query, including repeated queries.
Byte work is separate from this record-read counter. -/
set_option autoImplicit false
namespace AspisR1.BinFrameReplayReads
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8PairedCommitment FS FS2.Duplex
open RawCommitmentFrameReplay

/-- Unlike the cut's first-match scan, oracle replay returns the last write. -/
def lookup {I A : Type} [DecidableEq I] (a : I) :
    Option A → List (I × A) → Option A × Nat
  | current, [] => (current, 0)
  | current, (i, v) :: rest =>
    let r := lookup a (if a = i then some v else current) rest
    (r.1, r.2 + 1)

theorem lookup_value {I A : Type} [DecidableEq I] (a : I)
    (t : Table I A) (log : List (I × A)) :
    (lookup a (t a) log).1 = TraceTable.replay t log a := by
  induction log generalizing t with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨i, v⟩
    change (lookup a (if a = i then some v else t a) rest).1 =
      TraceTable.replay (put t i v) rest a
    have h : (if a = i then some v else t a) = put t i v a := by
      simp only [put]
    rw [h]
    exact ih _

theorem lookup_reads {I A : Type} [DecidableEq I] (a : I)
    (current : Option A) (log : List (I × A)) :
    (lookup a current log).2 = log.length := by
  induction log generalizing current with
  | nil => rfl
  | cons entry rest ih => simp only [lookup, ih, List.length_cons]

def oracle (log : List (Bytes × State)) (a : Bytes) : State × Nat :=
  let r := lookup a none log
  (r.1.getD default, r.2)

theorem oracle_value (log : List (Bytes × State)) (a : Bytes) :
    (oracle log a).1 = OracleProgramReplay.oracleOf log a := by
  change (lookup a ((emptyTable : Table Bytes State) a) log).1.getD default =
    (TraceTable.replay emptyTable log a).getD default
  rw [lookup_value]

theorem oracle_reads (log : List (Bytes × State)) (a : Bytes) :
    (oracle log a).2 = log.length := lookup_reads a none log

def payload (log : List (Bytes × State)) (pub : Public)
    (state : State) (row : Nat) (bytes : Bytes) : State × Nat :=
  let a := oracle log (RawTranscriptFrameBytes.absorb state row bytes)
  let b := oracle log (RawTranscriptFrameBytes.advance a.1)
  if row = 26 then
    let c := oracle log (RawTranscriptFrameBytes.reseed pub.tag b.1)
    (c.1, a.2 + b.2 + c.2)
  else (b.1, a.2 + b.2)

theorem payload_value (log : List (Bytes × State)) (pub : Public)
    (state : State) (row : Nat) (bytes : Bytes) :
    (payload log pub state row bytes).1 =
      payloadSuccessor (OracleProgramReplay.oracleOf log) pub state row bytes := by
  simp only [payload, payloadSuccessor, oracle_value]
  split <;> rfl

theorem payload_reads (log : List (Bytes × State)) (pub : Public)
    (state : State) (row : Nat) (bytes : Bytes) :
    (payload log pub state row bytes).2 ≤ 3 * log.length := by
  unfold payload
  split <;> simp only [oracle_reads] <;> omega

def successorCount (log : List (Bytes × State)) (pub : Public)
    (state : State) (row : Nat) (m : Message) : State × Nat :=
  match row, m with
  | 0, .initial root _ =>
    let a := oracle log (RawTranscriptFrameBytes.publicInit pub.pubBytes root)
    let b := oracle log (RawTranscriptFrameBytes.rowZero a.1)
    let c := oracle log (RawTranscriptFrameBytes.advance b.1)
    (c.1, a.2 + b.2 + c.2)
  | 0, _ => (zeroState, 0)
  | _ + 1, .initial _ _ => (zeroState, 0)
  | n + 1, .payload p => payload log pub state (n + 1) p.val
  | n + 1, .c2 p _ => payload log pub state (n + 1) p.val
  | n + 1, .second p _ => payload log pub state (n + 1) p.val

theorem successor_value (log : List (Bytes × State)) (pub : Public)
    (state : State) (row : Nat) (m : Message) :
    (successorCount log pub state row m).1 =
      successor (OracleProgramReplay.oracleOf log) pub state row m := by
  cases row <;> cases m <;>
    simp only [successorCount, successor, payload_value, oracle_value]

theorem successor_reads (log : List (Bytes × State)) (pub : Public)
    (state : State) (row : Nat) (m : Message) :
    (successorCount log pub state row m).2 ≤ 3 * log.length := by
  cases row <;> cases m <;>
    simp only [successorCount, oracle_reads]
  all_goals first | exact payload_reads _ _ _ _ _ | omega

def stateCount (log : List (Bytes × State)) (pub : Public) (pf : Proof) :
    Nat → State × Nat
  | 0 => (zeroState, 0)
  | n + 1 =>
    let prev := stateCount log pub pf n
    let next := successorCount log pub prev.1 n (pf n)
    (next.1, prev.2 + next.2)

theorem state_value (log : List (Bytes × State)) (pub : Public) (pf : Proof)
    (n : Nat) : (stateCount log pub pf n).1 =
      stateBefore (OracleProgramReplay.oracleOf log) pub pf n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stateCount, stateBefore, successor_value, ih]

theorem state_reads (log : List (Bytes × State)) (pub : Public) (pf : Proof)
    (n : Nat) : (stateCount log pub pf n).2 ≤ 3 * n * log.length := by
  induction n with
  | zero => simp [stateCount]
  | succ n ih =>
    have hs := successor_reads log pub (stateCount log pub pf n).1 n (pf n)
    change _ + _ ≤ _
    calc
      _ ≤ 3 * n * log.length + 3 * log.length := Nat.add_le_add ih hs
      _ = _ := by ring

def frameCount (run : RawCutProverCompiler.RunView) (row : Nat) : Bytes × Nat :=
  let s := stateCount run.1 run.2.1.1 run.2.1.2 row
  (frameAt run.2.1.1 s.1 row (run.2.1.2 row), s.2)

theorem frame_value (run : RawCutProverCompiler.RunView) (row : Nat) :
    (frameCount run row).1 = frameFromView run row := by
  simp only [frameCount, frameFromView, frame, state_value]

theorem frame_reads (run : RawCutProverCompiler.RunView) (row : Nat) :
    (frameCount run row).2 ≤ 3 * row * run.1.length :=
  state_reads _ _ _ _

theorem three_frames_reads (run : RawCutProverCompiler.RunView) :
    (frameCount run 0).2 + (frameCount run 2).2 + (frameCount run 30).2 ≤
      96 * run.1.length := by
  have h0 := frame_reads run 0
  have h2 := frame_reads run 2
  have h30 := frame_reads run 30
  omega

#print axioms lookup_value
#print axioms lookup_reads
#print axioms oracle_value
#print axioms oracle_reads
#print axioms payload_value
#print axioms payload_reads
#print axioms successor_value
#print axioms successor_reads
#print axioms state_value
#print axioms state_reads
#print axioms frame_value
#print axioms frame_reads
#print axioms three_frames_reads
end AspisR1.BinFrameReplayReads
