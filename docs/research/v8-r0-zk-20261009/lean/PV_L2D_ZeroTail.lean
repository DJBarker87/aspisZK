import Init

/-! Native V359 `validate_zero_tail` at its scalar-list boundary.
This does not assert the honest caller's field-domain invariant. -/
set_option autoImplicit false
namespace PV_L2D_ZeroTail

inductive Event where
  | loopTest (index : Nat) (inside : Bool)
  | read (index : Nat)
  | zeroTest (index : Nat) (zero : Bool)
  deriving DecidableEq, Repr

inductive Outcome where
  | ok
  | wrongField
  deriving DecidableEq, Repr

/-- `cells` is exactly the suffix starting at `index`. Reading an exhausted
suffix records the native loop's final false test, not another limb load. -/
def run : Nat → List Nat → Outcome × List Event
  | i, [] => (.ok, [.loopTest i false])
  | i, x :: xs =>
    if x = 0 then
      let r := run (i+1) xs
      (r.1, .loopTest i true :: .read i :: .zeroTest i true :: r.2)
    else (.wrongField, [.loopTest i true, .read i, .zeroTest i false])

def passing : Nat → Nat → List Event
  | i, 0 => [.loopTest i false]
  | i, n+1 => .loopTest i true :: .read i :: .zeroTest i true :: passing (i+1) n

theorem complete_zero (i n : Nat) :
    run i (List.replicate n 0) = (.ok, passing i n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, run, passing, ih]
#print axioms complete_zero

theorem complete_passing (i : Nat) (xs : List Nat)
    (h : ∀ x ∈ xs, x = 0) :
    run i xs = (.ok, passing i xs.length) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs, y = 0 := by
      intro y hy
      exact h y (by simp [hy])
    simp [run, hx, passing, ih (i+1) ht]
#print axioms complete_passing

theorem first_bad (i x : Nat) (xs : List Nat) (h : x ≠ 0) :
    run i (x :: xs) =
      (.wrongField, [.loopTest i true, .read i, .zeroTest i false]) := by
  simp [run, h]
#print axioms first_bad

theorem ok_iff (i : Nat) (xs : List Nat) :
    (run i xs).1 = .ok ↔ ∀ x ∈ xs, x = 0 := by
  induction xs generalizing i with
  | nil => simp [run]
  | cons x xs ih =>
    by_cases h : x = 0
    · simp [run, h, ih]
    · simp [run, h]
#print axioms ok_iff

theorem honest_trace (i : Nat) (xs ys : List Nat)
    (hx : ∀ x ∈ xs, x = 0) (hy : ∀ y ∈ ys, y = 0)
    (len : xs.length = ys.length) : run i xs = run i ys := by
  rw [complete_passing i xs hx, complete_passing i ys hy, len]
#print axioms honest_trace

/-- The lower field limbs can differ: validation reads only the excluded suffix.
The reference records all guards, limb addresses and early-error decisions. -/
def validate (limbs : List Nat) (first : Nat) := run first (limbs.drop first)

theorem lower_limbs_irrelevant (lo lo' tail : List Nat) (h : lo.length = lo'.length) :
    validate (lo ++ tail) lo.length = validate (lo' ++ tail) lo'.length := by
  simp [validate, List.drop_left, h]
#print axioms lower_limbs_irrelevant

theorem base_honest (lo : Nat) :
    validate (lo :: List.replicate 7 0) 1 = (.ok, passing 1 7) := by
  exact complete_zero 1 7
#print axioms base_honest

theorem secure_honest (a b c d : Nat) :
    validate ([a,b,c,d] ++ List.replicate 4 0) 4 = (.ok, passing 4 4) := by
  exact complete_zero 4 4
#print axioms secure_honest

theorem nonvacuous :
    validate (1 :: List.replicate 7 0) 1 = validate (2 :: List.replicate 7 0) 1 ∧
    validate (0 :: 1 :: List.replicate 6 0) 1 ≠ validate (0 :: List.replicate 7 0) 1 := by
  constructor
  · rw [base_honest, base_honest]
  · decide
#print axioms nonvacuous
end PV_L2D_ZeroTail
