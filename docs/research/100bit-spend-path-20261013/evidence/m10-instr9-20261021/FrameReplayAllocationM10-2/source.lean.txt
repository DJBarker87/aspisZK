import FrameConstructorAllocationM10
import BinFrameReplayTotalWork

set_option autoImplicit false
namespace AspisR1.FrameReplayAllocationM10
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8PairedCommitment FS FS2.Duplex RawCommitmentFrameReplay
open FrameConstructorAllocationM10

/-- One comparison result group, the updated option, and the replay result.
The query and retained state are referenced, never recursively copied. -/
def lookupCells (a : Bytes) : Option State → List (Bytes × State) → Nat
  | _, [] => 1
  | current, (i,v)::rest =>
    ListConstructorAllocationM10.equalCells a i+2+
      lookupCells a (if (BinLeafListWork.equal a i).1 then some v else current) rest

theorem lookup_work (a : Bytes) (current : Option State) (log : List (Bytes × State)) :
    lookupCells a current log ≤ (BinFrameLookupWork.lookup a current log).2 := by
  induction log generalizing current with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
    rcases entry with ⟨i,v⟩
    have he := ListConstructorAllocationM10.equal_work a i
    have ht := ih (if (BinLeafListWork.equal a i).1 then some v else current)
    change _+2+_ ≤ _+3+_
    omega

def ask (log : List (Bytes × State)) (a : Model Bytes) : Model State where
  run := BinFrameReplayTotalWork.ask log a.run
  cells := lookupCells a.run.1 none log+1+a.cells+2
  paid := by
    have hl := lookup_work a.run.1 none log
    have ha := a.paid
    change _ ≤ (BinFrameLookupWork.lookup a.run.1 none log).2+1+a.run.2+2
    omega

def payload (log : List (Bytes × State)) (pub : Public) (state : State)
    (row : Nat) (bytes : Bytes) : Model State :=
  let a := ask log (absorb state row bytes)
  let b := ask log (advance a.run.1)
  if row = 26 then
    let c := ask log (reseed pub.tag b.run.1)
    ⟨(c.run.1,a.run.2+b.run.2+c.run.2),a.cells+b.cells+c.cells,
      Nat.add_le_add (Nat.add_le_add a.paid b.paid) c.paid⟩
  else ⟨(b.run.1,a.run.2+b.run.2),a.cells+b.cells,Nat.add_le_add a.paid b.paid⟩

theorem payload_erase (log : List (Bytes × State)) (pub : Public) (state : State)
    (row : Nat) (bytes : Bytes) :
    (payload log pub state row bytes).run = BinFrameReplayTotalWork.payload log pub state row bytes := by
  by_cases h : row = 26 <;>
    simp only [payload,BinFrameReplayTotalWork.payload,h,if_true,if_false] <;> rfl

def successor (log : List (Bytes × State)) (pub : Public) (state : State) :
    Nat → Message → Model State
  | 0, .initial root _ =>
    let a := ask log (publicInit pub.pubBytes root)
    let b := ask log (rowZero a.run.1)
    let c := ask log (advance b.run.1)
    ⟨(c.run.1,a.run.2+b.run.2+c.run.2),a.cells+b.cells+c.cells,
      Nat.add_le_add (Nat.add_le_add a.paid b.paid) c.paid⟩
  | 0, _ => ⟨(zeroState,0),0,Nat.le_refl _⟩
  | _+1, .initial _ _ => ⟨(zeroState,0),0,Nat.le_refl _⟩
  | n+1, .payload p => payload log pub state (n+1) p.val
  | n+1, .c2 p _ => payload log pub state (n+1) p.val
  | n+1, .second p _ => payload log pub state (n+1) p.val

theorem successor_erase (log : List (Bytes × State)) (pub : Public) (state : State)
    (row : Nat) (m : Message) :
    (successor log pub state row m).run = BinFrameReplayTotalWork.successorWork log pub state row m := by
  cases row <;> cases m <;> first | rfl | exact payload_erase _ _ _ _ _

def state (log : List (Bytes × State)) (pub : Public) (pf : Proof) : Nat → Model State
  | 0 => ⟨(zeroState,0),0,Nat.le_refl _⟩
  | n+1 =>
    let a := state log pub pf n
    let b := successor log pub a.run.1 n (pf n)
    ⟨(b.run.1,a.run.2+b.run.2),a.cells+b.cells,Nat.add_le_add a.paid b.paid⟩

theorem state_erase (log : List (Bytes × State)) (pub : Public) (pf : Proof) (n : Nat) :
    (state log pub pf n).run = BinFrameReplayTotalWork.stateWork log pub pf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [state,BinFrameReplayTotalWork.stateWork,successor_erase,ih]

def frameAt (pub : Public) (s : State) : Nat → Message → Model Bytes
  | 0, .initial root _ => publicInit pub.pubBytes root
  | 0, _ => join (stateBytes zeroState) (literal [1])
  | _+1, .initial _ _ => join (stateBytes zeroState) (literal [1])
  | n+1, .payload p => absorb s (n+1) p.val
  | n+1, .c2 p _ => absorb s (n+1) p.val
  | n+1, .second p _ => absorb s (n+1) p.val

theorem frameAt_erase (pub : Public) (s : State) (row : Nat) (m : Message) :
    (frameAt pub s row m).run = BinFrameReplayTotalWork.frameAtWork pub s row m := by
  cases row <;> cases m <;> rfl

def frame (run : RawCutProverCompiler.RunView) (row : Nat) : Model Bytes :=
  let s := state run.1 run.2.1.1 run.2.1.2 row
  let f := frameAt run.2.1.1 s.run.1 row (run.2.1.2 row)
  ⟨(f.run.1,s.run.2+f.run.2),s.cells+f.cells,Nat.add_le_add s.paid f.paid⟩

theorem frame_erase (run : RawCutProverCompiler.RunView) (row : Nat) :
    (frame run row).run = BinFrameReplayTotalWork.frameWork run row := by
  simp only [frame,BinFrameReplayTotalWork.frameWork,frameAt_erase,state_erase]

theorem frame_cells_work (run : RawCutProverCompiler.RunView) (row : Nat) :
    (frame run row).cells ≤ (BinFrameReplayTotalWork.frameWork run row).2 := by
  rw [← frame_erase]
  exact (frame run row).paid

#print axioms lookup_work
#print axioms payload_erase
#print axioms successor_erase
#print axioms state_erase
#print axioms frameAt_erase
#print axioms frame_erase
#print axioms frame_cells_work
end AspisR1.FrameReplayAllocationM10
