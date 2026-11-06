import NLF_SnapshotEvents
set_option autoImplicit false
namespace NLF_SnapshotFold
open NLF_RefCell NLF_SdkModel NLF_ParentModel NLF_SnapshotEvents

def run (p : Parent) : List Nat → Parent × List (Except ProgramError Payload)
  | [] => (p,[])
  | a::as =>
    let r := step p a
    let tail := run r.1 as
    (tail.1,r.2::tail.2)

def schedule (s : State) (n : Nat) : List Nat → List Event
  | [] => []
  | a::as => events s a n ++ schedule s (n+1) as

def replies (s : State) (n : Nat) : List Nat → List (Except ProgramError Payload)
  | [] => []
  | a::as => (NLF_Bracket.snapshot s a n).2 :: replies s (n+1) as

theorem run_frame (p : Parent) (as : List Nat) : (run p as).1.state = p.state := by
  induction as generalizing p with
  | nil => rfl
  | cons a as ih =>
    change (run (step p a).1 as).1.state = p.state
    rw [ih,step_frame]

theorem run_next (p : Parent) (as : List Nat) : (run p as).1.next = p.next+as.length := by
  induction as generalizing p with
  | nil => simp [run]
  | cons a as ih =>
    change (run (step p a).1 as).1.next = p.next+(a::as).length
    rw [ih,step_next]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem run_invariant (p : Parent) (as : List Nat) (h : Invariant p) :
    Invariant (run p as).1 := by
  induction as generalizing p with
  | nil => exact h
  | cons a as ih => exact ih (step p a).1 (step_invariant p a h)

theorem run_events (p : Parent) (as : List Nat) :
    (run p as).1.events = p.events ++ schedule p.state p.next as := by
  induction as generalizing p with
  | nil => simp [run,schedule]
  | cons a as ih =>
    change (run (step p a).1 as).1.events = _
    rw [ih,step_frame,step_next]
    simp [step,schedule,List.append_assoc]

theorem run_replies (p : Parent) (as : List Nat) : (run p as).2 = replies p.state p.next as := by
  induction as generalizing p with
  | nil => rfl
  | cons a as ih =>
    change (step p a).2 :: (run (step p a).1 as).2 = _
    rw [ih,step_frame,step_next]
    rfl

#print axioms run_frame
#print axioms run_next
#print axioms run_invariant
#print axioms run_events
#print axioms run_replies
end NLF_SnapshotFold
