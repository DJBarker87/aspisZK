import PV_B3_EvalFold222
namespace PV_B3_Structural222
open Aeneas Aeneas.Std
set_option autoImplicit false
-- Representation lemmas for the structural native/copy argument. Arithmetic
-- callbacks are arbitrary; their calls are never commuted or reassociated.
theorem take_set_next {A : Type} (xs : List A) (i : Nat) (x : A) (h : i < xs.length) :
    (xs.set i x).take (i+1) = xs.take i ++ [x] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi : i < xs.length := by simpa using h
      simpa using congrArg (List.cons a) (ih i hi)

def scan {A : Type} (p : A → Bool) : Nat → List A → Nat
  | n, [] => n
  | n, x::xs => if p x then scan p (n-1) xs else n

theorem scan_value {A : Type} (p : A → Bool) (xs : List A) :
    ∀ n, xs.length ≤ n → scan p n xs = n-(xs.takeWhile p).length := by
  induction xs with
  | nil => intro n h; rfl
  | cons x xs ih =>
    intro n h
    by_cases hp : p x = true
    · simp only [scan, hp, Bool.true_eq, ↓reduceIte, List.takeWhile_cons_of_pos hp]
      rw [ih (n-1) (by simp only [List.length_cons] at h; omega)]
      simp only [List.length_cons]
      omega
    · have hf : p x = false := by cases hpx : p x <;> simp_all
      simp only [scan, hf, Bool.false_eq_true, ↓reduceIte, List.takeWhile_cons_of_neg hp,
        List.length_nil, Nat.sub_zero]

-- Prefix bound used by the fixed 1024-cell representation.
theorem prefix_bound {A : Type} (p : A → Bool) (xs : List A) :
    scan p xs.length xs ≤ xs.length := by
  rw [scan_value p xs xs.length (Nat.le_refl _)]
  exact Nat.sub_le _ _

#print axioms take_set_next
#print axioms scan_value
#print axioms prefix_bound
end PV_B3_Structural222
