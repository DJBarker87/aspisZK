import OraclePortFrozenOrderSlot

set_option autoImplicit false
namespace NJA_WellFormed
open AspisR1.OraclePortFrozenOrder
attribute [local instance] Classical.propDecidable

-- The windows(2).all predicate, unfolded one native window at a time.
def adjacent : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x < y ∧ adjacent (y :: rest)

theorem adjacent_pairwise (xs : List Nat) : adjacent xs ↔ xs.Pairwise (· < ·) := by
  induction xs with
  | nil => simp [adjacent]
  | cons x xs ih =>
    cases xs with
    | nil => simp [adjacent]
    | cons y rest =>
      simp only [adjacent] at ih ⊢
      rw [List.pairwise_cons]
      constructor
      · rintro ⟨xy, tail⟩
        have pw := ih.mp tail
        refine ⟨?_, pw⟩
        intro z mem
        rcases List.mem_cons.mp mem with eq | mem
        · simpa [eq] using xy
        · exact Nat.lt_trans xy ((List.pairwise_cons.mp pw).1 z mem)
      · rintro ⟨head, tail⟩
        exact ⟨head y (by simp), ih.mpr tail⟩

-- Same pure rejection order as Rust: length, adjacent order, leaf domain.
def source (xs : List Nat) : Bool :=
  if xs = [] then false else
  if xs.length > 16 then false else
  if adjacent xs then decide (∀ x ∈ xs, x < 262144) else false

theorem source_eq (xs : List Nat) : source xs = decide (wellFormed xs) := by
  unfold source wellFormed
  rw [← adjacent_pairwise]
  by_cases empty : xs = []
  · simp [empty]
  · by_cases large : xs.length > 16
    · simp [empty, large, show ¬ xs.length ≤ 16 by omega]
    · by_cases sorted : adjacent xs
      · simp [empty, large, sorted, show xs.length ≤ 16 by omega]
      · simp [empty, large, sorted]

#print axioms adjacent_pairwise
#print axioms source_eq
end NJA_WellFormed
