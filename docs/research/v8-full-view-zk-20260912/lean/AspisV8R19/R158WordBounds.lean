import Aeneas.Std

set_option autoImplicit false

namespace AspisV8R19.R158WordBounds

open Aeneas Aeneas.Std Result Aeneas.Std.WP

theorem checked_add_eq_wrapping (a b : U32)
    (h : a.val + b.val ≤ U32.max) :
    (a + b : Result U32) = Result.ok (U32.wrapping_add a b) := by
  have hchecked : (a + b : Result U32) ⦃ x => x.val = a.val + b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_UScalarTy_U32_eq] using h
  obtain ⟨x, hx, hxval⟩ := spec_imp_exists hchecked
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hxval, U32.wrapping_add_val_eq]
  have hsize : U32.max + 1 = UScalar.size .U32 := by
    simp [U32.max, U32.size, U32.numBits]
  have hlt : a.val + b.val < UScalar.size .U32 := by omega
  exact (Nat.mod_eq_of_lt hlt).symm

theorem checked_sub_eq_wrapping (a b : U32)
    (h : b.val ≤ a.val) :
    (a - b : Result U32) = Result.ok (U32.wrapping_sub a b) := by
  have hchecked : (a - b : Result U32) ⦃ x => x.val = a.val - b.val ∧ b.val ≤ a.val ⦄ := by
    exact UScalar.sub_spec h
  obtain ⟨x, hx, hxval⟩ := spec_imp_exists hchecked
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  rcases hxval with ⟨hxval, _⟩
  rw [hxval, U32.wrapping_sub_val_eq, UScalar.size_UScalarTyU32]
  have hsize : U32.max + 1 = UScalar.size .U32 := by
    simp [U32.max, U32.size, U32.numBits]
  have hscalarSize : UScalar.size .U32 = U32.size :=
    UScalar.size_UScalarTyU32
  have hbounda : a.val ≤ U32.max := by scalar_tac
  have hboundb : b.val ≤ U32.max := by scalar_tac
  have harg : a.val + (U32.size - b.val) =
      U32.size + (a.val - b.val) := by rw [← hscalarSize]; omega
  rw [harg]
  have hlt : a.val - b.val < U32.size := by omega
  rw [Nat.add_mod]
  simp [Nat.mod_eq_of_lt hlt]

theorem checked_add_u64_eq_wrapping (a b : U64)
    (h : a.val + b.val ≤ U64.max) :
    (a + b : Result U64) = Result.ok (U64.wrapping_add a b) := by
  have hchecked : (a + b : Result U64) ⦃ x => x.val = a.val + b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_UScalarTy_U64_eq] using h
  obtain ⟨x, hx, hxval⟩ := spec_imp_exists hchecked
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hxval, U64.wrapping_add_val_eq]
  have hsize : U64.max + 1 = UScalar.size .U64 := by
    simp [U64.max, U64.size, U64.numBits]
  have hlt : a.val + b.val < UScalar.size .U64 := by omega
  exact (Nat.mod_eq_of_lt hlt).symm

theorem checked_sub_u64_eq_wrapping (a b : U64)
    (h : b.val ≤ a.val) :
    (a - b : Result U64) = Result.ok (U64.wrapping_sub a b) := by
  have hchecked : (a - b : Result U64) ⦃ x => x.val = a.val - b.val ∧ b.val ≤ a.val ⦄ := by
    exact UScalar.sub_spec h
  obtain ⟨x, hx, hxval⟩ := spec_imp_exists hchecked
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  rcases hxval with ⟨hxval, _⟩
  rw [hxval, U64.wrapping_sub_val_eq, UScalar.size_UScalarTyU64]
  have hsize : U64.max + 1 = UScalar.size .U64 := by
    simp [U64.max, U64.size, U64.numBits]
  have hscalarSize : UScalar.size .U64 = U64.size :=
    UScalar.size_UScalarTyU64
  have hbounda : a.val ≤ U64.max := by scalar_tac
  have hboundb : b.val ≤ U64.max := by scalar_tac
  have harg : a.val + (U64.size - b.val) =
      U64.size + (a.val - b.val) := by rw [← hscalarSize]; omega
  rw [harg]
  have hlt : a.val - b.val < U64.size := by omega
  rw [Nat.add_mod]
  simp [Nat.mod_eq_of_lt hlt]

theorem checked_mul_u64_eq_wrapping (a b : U64)
    (h : a.val * b.val ≤ U64.max) :
    (a * b : Result U64) = Result.ok (U64.wrapping_mul a b) := by
  have hchecked : (a * b : Result U64) ⦃ x => x.val = a.val * b.val ⦄ := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_UScalarTy_U64_eq] using h
  obtain ⟨x, hx, hxval⟩ := spec_imp_exists hchecked
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hxval, U64.wrapping_mul_val_eq]
  have hsize : U64.max + 1 = UScalar.size .U64 := by
    simp [U64.max, U64.size, U64.numBits]
  have hlt : a.val * b.val < UScalar.size .U64 := by omega
  exact (Nat.mod_eq_of_lt hlt).symm

theorem wrapping_shr31_value (x : U64) :
    (U64.wrapping_shr x 31#u32).val = x.val >>> 31 := by
  have hshift : (31#u32).val % 64 = 31 := by
    have h31 : (31#u32 : U32).val = 31 := by scalar_tac
    rw [h31]
  calc
    (U64.wrapping_shr x 31#u32).val =
        (U64.wrapping_shr x 31#u32).bv.toNat := by
      exact (UScalar.bv_toNat _).symm
    _ = (x.bv.ushiftRight 31).toNat := by
      rw [U64.wrapping_shr_bv_eq]
      rw [hshift]
    _ = x.bv.toNat >>> 31 := BitVec.toNat_ushiftRight _ _
    _ = x.val >>> 31 := by rw [UScalar.bv_toNat]

#print axioms checked_add_eq_wrapping
#print axioms checked_sub_eq_wrapping
#print axioms checked_add_u64_eq_wrapping
#print axioms checked_sub_u64_eq_wrapping
#print axioms checked_mul_u64_eq_wrapping
#print axioms wrapping_shr31_value

end AspisV8R19.R158WordBounds
