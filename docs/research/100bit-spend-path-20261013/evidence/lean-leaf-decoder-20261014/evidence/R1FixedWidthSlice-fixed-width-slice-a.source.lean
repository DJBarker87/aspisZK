import Mathlib.Data.List.OfFn

/-! Recover one equal-width block from a flattened list encoding. -/
set_option autoImplicit false

namespace AspisR1.FixedWidthSlice

theorem flatMap_slice {A B : Type} (f : A → List B) (k : Nat)
    (hlen : ∀ a, (f a).length = k) (xs : List A) (i : Nat)
    (hi : i < xs.length) :
    ((xs.flatMap f).drop (k * i)).take k = f xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a as ih =>
      cases i with
      | zero =>
          simp only [Nat.mul_zero, List.flatMap_cons, List.drop_zero]
          rw [List.take_append_of_le_length (by rw [hlen a])]
          exact List.take_of_length_le (by rw [hlen a])
      | succ i =>
          have hi' : i < as.length := by simpa using hi
          rw [Nat.mul_succ]
          simp only [List.flatMap_cons]
          rw [List.drop_append_of_le_length (by rw [hlen a]; omega)]
          have hdrop : k * i + k - (f a).length = k * i := by rw [hlen a]; omega
          rw [hdrop]
          simpa [List.getElem_cons_succ] using ih i hi'

theorem ofFn_flatMap_slice {A B : Type} (m : Nat) (f : A → List B)
    (k : Nat) (hlen : ∀ a, (f a).length = k) (xs : Fin m → A) (i : Fin m) :
    (((List.ofFn xs).flatMap f).drop (k * i.val)).take k = f (xs i) := by
  have h := flatMap_slice f k hlen (List.ofFn xs) i.val (by simpa using i.isLt)
  simpa [List.getElem_ofFn] using h

#print axioms flatMap_slice
#print axioms ofFn_flatMap_slice

end AspisR1.FixedWidthSlice
