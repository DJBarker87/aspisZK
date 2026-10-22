import Aeneas.Std

set_option autoImplicit false

namespace AspisV8R19.R152WrappingBounds

open Aeneas Aeneas.Std Result Aeneas.Std.WP

theorem checked_add_eq_wrapping (a b : Usize)
    (h : a.val + b.val ≤ Usize.max) :
    (a + b : Result Usize) = .ok (Std.Usize.wrapping_add a b) := by
  have hchecked : (a + b : Result Usize) ⦃ x => x.val = a.val + b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using h
  obtain ⟨x, hx, hxval⟩ := spec_imp_exists hchecked
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hxval, Std.Usize.wrapping_add_val_eq]
  have hsize : Usize.max + 1 = UScalar.size .Usize := by
    simp [Usize.max, Usize.size, Usize.numBits]
  have hlt : a.val + b.val < UScalar.size .Usize := by omega
  exact (Nat.mod_eq_of_lt hlt).symm

theorem checked_mul_eq_wrapping (a b : Usize)
    (h : a.val * b.val ≤ Usize.max) :
    (a * b : Result Usize) = .ok (Std.Usize.wrapping_mul a b) := by
  have hchecked : (a * b : Result Usize) ⦃ x => x.val = a.val * b.val ⦄ := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq] using h
  obtain ⟨x, hx, hxval⟩ := spec_imp_exists hchecked
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hxval, Std.Usize.wrapping_mul_val_eq]
  have hsize : Usize.max + 1 = UScalar.size .Usize := by
    simp [Usize.max, Usize.size, Usize.numBits]
  have hlt : a.val * b.val < UScalar.size .Usize := by omega
  exact (Nat.mod_eq_of_lt hlt).symm

#print axioms checked_add_eq_wrapping
#print axioms checked_mul_eq_wrapping

end AspisV8R19.R152WrappingBounds
