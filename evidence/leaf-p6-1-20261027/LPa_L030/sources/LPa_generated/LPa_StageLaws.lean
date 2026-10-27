import LPa_Fold
import LPa_Map
import LPa_FirstError
set_option autoImplicit false
namespace LPa

theorem stages_congr {S : Type} (a b : S → Nat → S) (initial : S) (n : Nat)
    (same : ∀ state i, i < n → a state i = b state i) :
    stages a initial n = stages b initial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have small : ∀ state i, i < n → a state i = b state i := by
      intro state i hi
      exact same state i (Nat.lt.step hi)
    simp only [stages, ih small]
    exact same _ _ (Nat.lt_succ_self _)

theorem firstBad_bound (bad : Nat → Bool) (n i : Nat)
    (hit : firstBad bad n = some i) : i < n := by
  rw [firstBad_find] at hit
  exact List.mem_range.mp (List.mem_of_find?_eq_some hit)

theorem firstBad_none (bad : Nat → Bool) (n : Nat) :
    firstBad bad n = none ↔ ∀ i, i < n → bad i = false := by
  rw [firstBad_find, List.find?_eq_none]
  simp only [List.mem_range, Bool.not_eq_true]

theorem firstBad_is_bad (bad : Nat → Bool) (n i : Nat)
    (hit : firstBad bad n = some i) : bad i = true := by
  rw [firstBad_find] at hit
  exact List.find?_some hit

theorem build_length {A : Type} (f : Nat → A) (n : Nat) : (build f n).length = n := by
  rw [build_map]
  simp only [List.length_map, List.length_range]

#print axioms stages_congr
#print axioms firstBad_bound
#print axioms firstBad_none
#print axioms firstBad_is_bad
#print axioms build_length
end LPa
