import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Capped rejection at the Option-candidate interface. `none` means reject;
`some a` means accept a. The uniform-word association is a separate obligation. -/
set_option autoImplicit false
namespace PV_L2B_Rejection

def scan {A : Type} : Nat → List (Option A) → Nat × Option A
  | 0, _ => (0, none)
  | _ + 1, [] => (0, none)
  | n + 1, none :: xs => let r := scan n xs; (r.1 + 1, r.2)
  | _ + 1, some a :: _ => (1, some a)

theorem cap_zero {A : Type} (xs : List (Option A)) : scan 0 xs = (0, none) := rfl
#print axioms cap_zero
theorem empty {A : Type} (n : Nat) : scan (n+1) ([] : List (Option A)) = (0, none) := rfl
#print axioms empty
theorem accepted {A : Type} (n : Nat) (a : A) (xs : List (Option A)) : scan (n+1) (some a :: xs) = (1, some a) := rfl
#print axioms accepted
theorem rejected {A : Type} (n : Nat) (xs : List (Option A)) : scan (n+1) (none :: xs) = ((scan n xs).1+1, (scan n xs).2) := rfl
#print axioms rejected
theorem consumed_le_cap {A : Type} (n : Nat) (xs : List (Option A)) : (scan n xs).1 ≤ n := by
  induction n generalizing xs with
  | zero => simp [scan]
  | succ n ih =>
    cases xs with
    | nil => simp [scan]
    | cons x xs => cases x <;> simp [scan]; exact ih xs
#print axioms consumed_le_cap
theorem consumed_le_length {A : Type} (n : Nat) (xs : List (Option A)) : (scan n xs).1 ≤ xs.length := by
  induction n generalizing xs with
  | zero => simp [scan]
  | succ n ih =>
    cases xs with
    | nil => simp [scan]
    | cons x xs => cases x <;> simp [scan]; exact ih xs
#print axioms consumed_le_length
theorem scan_map {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) :
    scan n (xs.map (Option.map f)) = ((scan n xs).1, (scan n xs).2.map f) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs => cases x <;> simp [scan, ih]
#print axioms scan_map
theorem count_map {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) :
    (scan n (xs.map (Option.map f))).1 = (scan n xs).1 := by rw [scan_map]
#print axioms count_map
theorem status_map {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) :
    (scan n (xs.map (Option.map f))).2.isSome = (scan n xs).2.isSome := by
  rw [scan_map]; cases (scan n xs).2 <;> rfl
#print axioms status_map
def trace {A : Type} (n : Nat) (xs : List (Option A)) : Nat × Bool :=
  ((scan n xs).1, (scan n xs).2.isSome)
theorem trace_relabel {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) :
    trace n (xs.map (Option.map f)) = trace n xs := by
  simp only [trace, count_map, status_map]
#print axioms trace_relabel
def flags {A : Type} (xs : List (Option A)) : List (Option Unit) := xs.map (Option.map (fun _ => ()))
theorem coins_only {A : Type} (n : Nat) (xs : List (Option A)) :
    trace n xs = trace n (flags xs) := (trace_relabel (fun _ => ()) n xs).symm
#print axioms coins_only
theorem same_flags {A B : Type} (n : Nat) (xs : List (Option A)) (ys : List (Option B))
    (h : flags xs = flags ys) : trace n xs = trace n ys := by
  rw [coins_only n xs, coins_only n ys, h]
#print axioms same_flags
theorem rejected_prefix {A : Type} (r n : Nat) (xs : List (Option A)) :
    scan (r+n) (List.replicate r none ++ xs) =
      (r + (scan n xs).1, (scan n xs).2) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.succ_add, List.replicate_succ, List.cons_append, rejected, ih]
    simp only [Nat.succ_add, Nat.add_succ]
#print axioms rejected_prefix
theorem first_accept {A : Type} (r n : Nat) (a : A) (xs : List (Option A)) :
    scan (r+n+1) (List.replicate r none ++ some a :: xs) = (r+1, some a) := by
  rw [show r+n+1=r+(n+1) by omega, rejected_prefix, accepted]
#print axioms first_accept
theorem exhausted {A : Type} (n : Nat) :
    scan n (List.replicate n (none : Option A)) = (n, none) := by
  have h := rejected_prefix (A := A) n 0 []
  simpa [scan] using h
#print axioms exhausted
theorem accept_in_range (p x : Nat) (h : x < p) :
    (if x < p then some x else none) = some x := if_pos h
#print axioms accept_in_range
theorem reject_at_boundary (p : Nat) :
    (if p < p then some p else none : Option Nat) = none := by simp
#print axioms reject_at_boundary
end PV_L2B_Rejection
