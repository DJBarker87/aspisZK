import PV_L2E_ArrayDivision
set_option autoImplicit false
namespace PV_L2E_ArrayDivisionTrace
open PV_L2E_ArrayMemory PV_L2E_ArrayDivision PV_L2D_DivisionBounds

inductive Event where
  | loopGuard (remaining : Nat) (live : Bool)
  | readGuard (index : Nat) (valid : Bool)
  | read (index : Nat)
  | divideGuard (nonzero : Bool)
  | writeGuard (index : Nat) (valid : Bool)
  | write (index : Nat)
  deriving DecidableEq

/-- Includes both Rust array bounds checks and the nonzero-divisor check.
Compiler removal of redundant guards is retained at V370. -/
def execute (width : Nat) : Nat → Nat → Memory → (Memory × Nat) × List Event
  | 0,r,a => ((a,r),[.loopGuard 0 false])
  | n+1,r,a =>
    let d := step r (a n)
    let rest := execute width n d.remainder (store a n d.quotient)
    (rest.1,[.loopGuard (n+1) true,.readGuard n (decide (n<width)),.read n,
      .divideGuard (decide (P≠0)),.writeGuard n (decide (n<width)),.write n] ++ rest.2)

def plan (width : Nat) : Nat → List Event
  | 0 => [.loopGuard 0 false]
  | n+1 => [.loopGuard (n+1) true,.readGuard n (decide (n<width)),.read n,
      .divideGuard true,.writeGuard n (decide (n<width)),.write n] ++ plan width n

theorem complete (width n r : Nat) (a : Memory) :
    execute width n r a=(run n r a,plan width n) := by
  induction n generalizing r a with
  | zero => rfl
  | succ n ih => simp only [execute,ih,run,plan]; rfl

def Safe : Event → Prop
  | .readGuard _ valid | .writeGuard _ valid | .divideGuard valid => valid=true
  | _ => True

theorem plan_safe (width n : Nat) (cap : n≤width) :
    ∀ e∈plan width n,Safe e := by
  induction n with
  | zero => simp [plan,Safe]
  | succ n ih =>
    have hn : n<width := by omega
    have ht := ih (by omega)
    simp only [plan,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intro e he
    rcases he with (rfl|rfl|rfl|rfl|rfl|rfl)|he <;> simp_all [Safe]

theorem all_guards_pass (width n r : Nat) (a : Memory) (cap : n≤width) :
    ∀ e∈(execute width n r a).2,Safe e := by
  rw [complete]
  exact plan_safe width n cap

#print axioms complete
#print axioms plan_safe
#print axioms all_guards_pass
end PV_L2E_ArrayDivisionTrace
