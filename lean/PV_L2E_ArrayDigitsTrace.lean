import PV_L2E_ArrayDigits
set_option autoImplicit false
namespace PV_L2E_ArrayDigitsTrace
open PV_L2E_ArrayMemory

inductive Event where
  | outerGuard (digit : Nat) (live : Bool)
  | pass (event : PV_L2E_ArrayDivisionTrace.Event)
  | digitGuard (digit : Nat) (valid : Bool)
  | writeDigit (digit : Nat)
  deriving DecidableEq

/-- Explicit outer digit loop. Fixed-size array copies at call boundaries
are separate from these direct-index operations and stay in native binding. -/
def execute (width count : Nat) : Nat → Nat → Memory → (Memory × List Nat) × List Event
  | i,0,a => ((a,[]),[.outerGuard i false])
  | i,n+1,a =>
    let p := PV_L2E_ArrayDivisionTrace.execute width width 0 a
    let tail := execute width count (i+1) n p.1.1
    ((tail.1.1,p.1.2::tail.1.2),[.outerGuard i true] ++ p.2.map Event.pass ++
      [.digitGuard i (decide (i<count)),.writeDigit i] ++ tail.2)

def plan (width count : Nat) : Nat → Nat → List Event
  | i,0 => [.outerGuard i false]
  | i,n+1 => [.outerGuard i true] ++
      (PV_L2E_ArrayDivisionTrace.plan width width).map Event.pass ++
      [.digitGuard i (decide (i<count)),.writeDigit i] ++ plan width count (i+1) n

theorem complete (width count i n : Nat) (a : Memory) :
    execute width count i n a=(PV_L2E_ArrayDigits.run width n a,plan width count i n) := by
  induction n generalizing i a with
  | zero => rfl
  | succ n ih =>
    simp only [execute,PV_L2E_ArrayDivisionTrace.complete,ih,PV_L2E_ArrayDigits.run,plan]

def Safe : Event → Prop
  | .pass e => PV_L2E_ArrayDivisionTrace.Safe e
  | .digitGuard _ valid => valid=true
  | _ => True

theorem plan_safe (width count i n : Nat) (cap : i+n≤count) :
    ∀ e∈plan width count i n,Safe e := by
  induction n generalizing i with
  | zero => simp [plan,Safe]
  | succ n ih =>
    have hp := PV_L2E_ArrayDivisionTrace.plan_safe width width (by omega)
    have ht := ih (i+1) (by omega)
    simp only [plan,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc]
    intro e he
    rcases he with rfl|he|rfl|rfl|he
    · trivial
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
      exact hp v hv
    · simp only [Safe,decide_eq_true_eq]; omega
    · trivial
    · exact ht e he

#print axioms complete
#print axioms plan_safe
end PV_L2E_ArrayDigitsTrace
