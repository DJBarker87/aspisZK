import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_QueryScan

structure State where
  accepted : List Nat
  draws : Nat
  deriving DecidableEq, Repr

inductive Event where
  | wordGuard (accepted draws : Nat) (stop : Bool)
  | compare (index : Nat) (equal : Bool)
  | write (index : Nat)
  | endBlock
  deriving DecidableEq, Repr

def member (x : Nat) : Nat → List Nat → Bool × List Event
  | _, [] => (false, [])
  | i, y::ys =>
    if x=y then (true, [.compare i true])
    else let t := member x (i+1) ys; (t.1, .compare i false :: t.2)

theorem member_value (x i : Nat) (ys : List Nat) :
    (member x i ys).1 = decide (x ∈ ys) := by
  induction ys generalizing i with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x=y
    · simp [member,h]
    · simp [member,h,ih,eq_comm]
#print axioms member_value

def stopped (s : State) : Bool := decide (s.accepted.length=22 ∨ s.draws=64)
def next (s : State) (x : Nat) : State :=
  ⟨if x ∈ s.accepted then s.accepted else s.accepted ++ [x], s.draws+1⟩

/-- Exact pre-word stop placement: an empty block executes no guard. -/
def scan : State → List Nat → Bool × State
  | s, [] => (false,s)
  | s, x::xs => if stopped s then (true,s) else scan (next s x) xs

def execute : State → List Nat → (Bool × State) × List Event
  | s, [] => ((false,s), [.endBlock])
  | s, x::xs =>
    if stopped s then ((true,s), [.wordGuard s.accepted.length s.draws true])
    else
      let m := member x 0 s.accepted
      let after := State.mk (if m.1 then s.accepted else s.accepted ++ [x]) (s.draws+1)
      let tail := execute after xs
      (tail.1, .wordGuard s.accepted.length s.draws false ::
        (m.2 ++ (if m.1 then [] else [.write s.accepted.length]) ++ tail.2))

theorem complete (s : State) (xs : List Nat) : (execute s xs).1 = scan s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [execute,scan]
    split
    · rfl
    · simp only [member_value]
      simpa only [next, decide_eq_true_eq] using ih (next s x)
#print axioms complete

theorem no_empty_guard (s : State) : execute s [] = ((false,s),[.endBlock]) := rfl
#print axioms no_empty_guard

theorem exact_stop (s : State) (x : Nat) (xs : List Nat) (h : stopped s=true) :
    execute s (x::xs) = ((true,s), [.wordGuard s.accepted.length s.draws true]) := by
  simp [execute,h]
#print axioms exact_stop

/-- Native completion-at-block-boundary behavior. The last accepted word
returns false; the next block performs the success guard. -/
theorem boundary (s : State) (x : Nat) (h : stopped s=false) :
    (execute s [x]).1 = (false,next s x) := by
  rw [complete]
  simp [scan,h]
#print axioms boundary

/-- `simE` needs the full candidate blocks, not only the accepted set. These
nonempty finite controls expose the missing history if that quotient is used. -/
theorem duplicate_history_matters :
    (execute ⟨[1],1⟩ [1,2]).1.2.accepted =
      (execute ⟨[1],1⟩ [2,2]).1.2.accepted ∧
    (execute ⟨[1],1⟩ [1,2]).2 ≠ (execute ⟨[1],1⟩ [2,2]).2 := by
  decide
#print axioms duplicate_history_matters

theorem complete_replay (s t : State) (xs ys : List Nat)
    (hs : s=t) (hw : xs=ys) : execute s xs = execute t ys := by
  cases hs; cases hw; rfl
#print axioms complete_replay
end PV_L2D_QueryScan
