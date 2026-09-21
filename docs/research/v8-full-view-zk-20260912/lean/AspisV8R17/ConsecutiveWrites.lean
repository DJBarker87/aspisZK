import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Lean.Elab.Tactic.Omega

/-! Sequential table writes. Bounds and noninterference are symbolic in
the list lengths; no concrete 271-entry update chain is normalized. -/
set_option autoImplicit false
namespace AspisV8R17
variable {A : Type*}

def writeConsecutive : List A → ℕ → (ℕ → A) → (ℕ → A)
  | [], _, table => table
  | x::xs, start, table => writeConsecutive xs (start+1) (Function.update table start x)

theorem writeConsecutive_outside (xs : List A) (start : ℕ) (table : ℕ → A)
    (j : ℕ) (h : j<start ∨ start+xs.length≤j) :
    writeConsecutive xs start table j = table j := by
  induction xs generalizing start table with
  | nil => rfl
  | cons x xs ih =>
    have ht : j<start+1 ∨ start+1+xs.length≤j := by simp only [List.length_cons] at h; omega
    have hn : j≠start := by simp only [List.length_cons] at h; omega
    rw [writeConsecutive, ih (start+1) _ ht, Function.update_of_ne hn]

theorem writeConsecutive_inside (xs : List A) (start : ℕ) (table : ℕ → A)
    (j : ℕ) (hj : j<xs.length) :
    writeConsecutive xs start table (start+j) = xs[j] := by
  induction xs generalizing start table j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, writeConsecutive, List.getElem_cons_zero]
      rw [writeConsecutive_outside _ _ _ _ (Or.inl (by omega))]
      simp
    | succ j =>
      have h : j<xs.length := by simpa using hj
      simpa only [writeConsecutive, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        List.getElem_cons_succ] using ih (start+1) (Function.update table start x) j h

theorem writeConsecutive_inside_at (xs : List A) (start : ℕ) (table : ℕ → A)
    (j : ℕ) (lo : start≤j) (hi : j<start+xs.length) :
    writeConsecutive xs start table j = xs[j-start]'(by omega) := by
  have h := writeConsecutive_inside xs start table (j-start) (by omega)
  simpa [Nat.add_sub_of_le lo] using h

theorem writeConsecutive_append (xs ys : List A) (start : ℕ) (table : ℕ → A) :
    writeConsecutive (xs++ys) start table =
      writeConsecutive ys (start+xs.length) (writeConsecutive xs start table) := by
  induction xs generalizing start table with
  | nil => simp [writeConsecutive]
  | cons x xs ih => simp [writeConsecutive, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem writeConsecutive_adjacent_commute (xs ys : List A) (start : ℕ) (table : ℕ → A) :
    writeConsecutive xs start (writeConsecutive ys (start+xs.length) table) =
      writeConsecutive ys (start+xs.length) (writeConsecutive xs start table) := by
  funext j
  by_cases h0 : j<start
  · rw [writeConsecutive_outside _ _ _ _ (Or.inl h0),
      writeConsecutive_outside _ _ _ _ (Or.inl (by omega)),
      writeConsecutive_outside _ _ _ _ (Or.inl (by omega)),
      writeConsecutive_outside _ _ _ _ (Or.inl h0)]
  by_cases h1 : j<start+xs.length
  · rw [writeConsecutive_inside_at xs start _ j (by omega) h1,
      writeConsecutive_outside ys _ _ j (Or.inl h1),
      writeConsecutive_inside_at xs start _ j (by omega) h1]
  by_cases h2 : j<start+xs.length+ys.length
  · rw [writeConsecutive_outside xs start _ j (Or.inr (by omega)),
      writeConsecutive_inside_at ys _ _ j (by omega) h2,
      writeConsecutive_inside_at ys _ _ j (by omega) h2]
  · rw [writeConsecutive_outside xs start _ j (Or.inr (by omega)),
      writeConsecutive_outside ys _ _ j (Or.inr (by omega)),
      writeConsecutive_outside ys _ _ j (Or.inr (by omega)),
      writeConsecutive_outside xs start _ j (Or.inr (by omega))]

#print axioms writeConsecutive_outside
#print axioms writeConsecutive_inside
#print axioms writeConsecutive_inside_at
#print axioms writeConsecutive_append
#print axioms writeConsecutive_adjacent_commute
end AspisV8R17
