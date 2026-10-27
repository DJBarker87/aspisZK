import Lean
namespace R1Z.PV_Canon
/-- The representative bound, independent of Rust integer implementation. -/
def P : Nat := 2147483647
def fold31 (x : Nat) : Nat := x % 2147483648 + x / 2147483648
def subtractP (x : Nat) : Nat := if x ≥ P then x - P else x
def reduce64 (x : Nat) : Nat := subtractP (fold31 (fold31 x))
theorem first_fold_bound (x : Nat) (hx : x < 18446744073709551616) :
    fold31 x ≤ 10737418238 := by
  unfold fold31
  have := Nat.mod_lt x (by omega : 0 < 2147483648)
  have : x / 2147483648 ≤ 8589934591 := by omega
  omega
theorem second_fold_bound (x : Nat) (hx : x ≤ 10737418238) :
    fold31 x ≤ 2147483651 := by
  unfold fold31
  have := Nat.mod_lt x (by omega : 0 < 2147483648)
  have : x / 2147483648 ≤ 4 := by omega
  omega
theorem subtract_canonical (x : Nat) (hx : x < 2 * P) : subtractP x < P := by
  unfold subtractP P at *
  split <;> omega
theorem reduce64_canonical (x : Nat) (hx : x < 18446744073709551616) :
    reduce64 x < P := by
  apply subtract_canonical
  have := second_fold_bound _ (first_fold_bound x hx)
  unfold P
  omega
#print axioms first_fold_bound
#print axioms second_fold_bound
#print axioms subtract_canonical
#print axioms reduce64_canonical
end R1Z.PV_Canon
