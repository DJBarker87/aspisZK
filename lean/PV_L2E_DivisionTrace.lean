import PV_L2D_DivisionBounds
set_option autoImplicit false
namespace PV_L2E_DivisionTrace
open PV_L2D_DivisionBounds

/-- Normalized source events: the loop's bound and each array read/write.
Arithmetic operands are values, not access addresses. -/
inductive Event where
  | guard (remaining : Nat) (taken : Bool)
  | read (index : Nat)
  | write (index : Nat)
  deriving DecidableEq

def plan : Nat → List Event
  | 0 => [.guard 0 false]
  | n+1 => [.guard (n+1) true,.read n,.write n] ++ plan n

/-- The list is in reverse array traversal order. Quotient writes use the
new word; no mutable restoration continuation is discarded. -/
def run : Nat → Nat → List Nat → (List Nat × Nat) × List Event
  | 0,r,_ => (([],r),[.guard 0 false])
  | n+1,r,[] => (([],r),[.guard (n+1) true])
  | n+1,r,x::xs =>
    let d := step r x
    let tail := run n d.remainder xs
    ((d.quotient::tail.1.1,tail.1.2),
      [.guard (n+1) true,.read n,.write n] ++ tail.2)

theorem exact (r : Nat) (xs : List Nat) :
    run xs.length r xs = (pass r xs,plan xs.length) := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons,run,ih,pass,plan]

/-- For valid fixed-width arrays the access pattern is independent of words
and of the incoming remainder, not merely equal on successful fixtures. -/
theorem trace_constant (r : Nat) (xs : List Nat) :
    (run xs.length r xs).2 = plan xs.length := congrArg Prod.snd (exact r xs)

theorem complete_value (r : Nat) (xs : List Nat) :
    (run xs.length r xs).1 = pass r xs := congrArg Prod.fst (exact r xs)

theorem safe (r : Nat) (xs : List Nat) (hr : r<P) (hx : ∀ x∈xs,x<B) :
    (∀ y∈(run xs.length r xs).1.1,y<B) ∧ (run xs.length r xs).1.2<P := by
  rw [complete_value]
  exact pass_bounds r xs hr hx

theorem same_width (r s : Nat) (xs ys : List Nat) (h : xs.length=ys.length) :
    (run xs.length r xs).2 = (run ys.length s ys).2 := by
  rw [trace_constant,trace_constant,h]

#print axioms exact
#print axioms trace_constant
#print axioms complete_value
#print axioms safe
#print axioms same_width
end PV_L2E_DivisionTrace
