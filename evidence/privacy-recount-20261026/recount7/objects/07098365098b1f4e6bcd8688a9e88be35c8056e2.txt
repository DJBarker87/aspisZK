import Aeneas.Std
namespace PV_B3_SmallUsizeD336
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem add (a b c : Usize) (h : a.val + b.val = c.val) :
    Usize.wrapping_add a b = c := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
  change (a.val + b.val) % Usize.size = c.val
  have hc : c.val < Usize.size := by simpa only [UScalar.size_UScalarTyUsize] using c.hSize
  rw [h,Nat.mod_eq_of_lt hc]

theorem mul (a b c : Usize) (h : a.val * b.val = c.val) :
    Usize.wrapping_mul a b = c := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_mul_val_eq, UScalar.size_UScalarTyUsize]
  change (a.val * b.val) % Usize.size = c.val
  have hc : c.val < Usize.size := by simpa only [UScalar.size_UScalarTyUsize] using c.hSize
  rw [h,Nat.mod_eq_of_lt hc]

#print axioms add
#print axioms mul
end PV_B3_SmallUsizeD336
