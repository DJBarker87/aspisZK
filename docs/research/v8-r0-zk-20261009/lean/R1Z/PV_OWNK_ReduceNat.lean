import Aeneas
set_option autoImplicit false
namespace R1Z.PV_OWNK_ReduceNat
def P : Nat := 2147483647
def fold31 (x : Nat) : Nat := x % 2147483648 + x / 2147483648
def subtractP (x : Nat) : Nat := if x ≥ P then x-P else x
def reduce64 (x : Nat) : Nat := subtractP (fold31 (fold31 x))
theorem first_bound (x : Nat) (hx : x < 18446744073709551616) :
 fold31 x ≤ 10737418238 := by
 unfold fold31
 have := Nat.mod_lt x (by omega : 0 < 2147483648)
 have : x / 2147483648 ≤ 8589934591 := by omega
 omega
theorem second_bound (x : Nat) (hx : x ≤ 10737418238) :
 fold31 x ≤ 2147483651 := by
 unfold fold31
 have := Nat.mod_lt x (by omega : 0 < 2147483648)
 have : x / 2147483648 ≤ 4 := by omega
 omega
theorem canonical (x : Nat) (hx : x < 18446744073709551616) : reduce64 x < P := by
 have := second_bound _ (first_bound x hx)
 unfold reduce64 subtractP P
 split <;> omega
theorem fold_mod (x : Nat) : fold31 x % P = x % P := by
 have h := Nat.mod_add_div x 2147483648
 have he : fold31 x + P * (x / 2147483648) = x := by unfold fold31 P; omega
 calc
  fold31 x % P = (fold31 x + P * (x / 2147483648)) % P := by
   rw [Nat.add_mod,Nat.mul_mod]; simp
  _ = x % P := congrArg (fun y => y % P) he
theorem subtract_mod (x : Nat) : subtractP x % P = x % P := by
 unfold subtractP
 split
 · rename_i h
   calc
    (x-P)%P = ((x-P)+P)%P := (Nat.add_mod_right (x-P) P).symm
    _ = x%P := congrArg (fun y => y%P) (Nat.sub_add_cancel h)
 · rfl
theorem exact_mod (x : Nat) (hx : x < 18446744073709551616) : reduce64 x = x % P := by
 have h : reduce64 x % P = x % P := by
  unfold reduce64
  rw [subtract_mod,fold_mod,fold_mod]
 rw [Nat.mod_eq_of_lt (canonical x hx)] at h
 exact h
#print axioms first_bound
#print axioms second_bound
#print axioms canonical
#print axioms fold_mod
#print axioms subtract_mod
#print axioms exact_mod
end R1Z.PV_OWNK_ReduceNat
