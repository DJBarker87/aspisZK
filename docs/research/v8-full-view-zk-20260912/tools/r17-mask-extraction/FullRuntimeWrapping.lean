import AspisV8R17.UnsignedReducerOps

/-! Checked/wrapping bridges in the actual cached runtime. Each needed bound
is explicit; no caller is allowed to silently assume these operations agree. -/
namespace AspisV8R17.FullRuntimeWrapping
open Aeneas.Std

theorem add_agree (x y : U64) (h : x.val + y.val < 2^64) :
    UScalar.add x y = .ok (U64.wrapping_add x y) := by
  obtain ⟨z, hz, hv⟩ := UnsignedCoreSlice.add_success x y h
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [U64.wrapping_add_val_eq]
  have hs : UScalar.size .U64 = 2^64 := by simp [UScalar.size, U64.size, U64.numBits]
  rw [hs]
  change z.val = (x.val + y.val) % 2^64
  rw [hv, Nat.mod_eq_of_lt h]

theorem mul_agree (x y : U64) (h : x.val * y.val < 2^64) :
    UScalar.mul x y = .ok (U64.wrapping_mul x y) := by
  obtain ⟨z, hz, hv⟩ := UnsignedCoreSlice.mul_success x y h
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [U64.wrapping_mul_val_eq]
  have hs : UScalar.size .U64 = 2^64 := by simp [UScalar.size, U64.size, U64.numBits]
  rw [hs]
  change z.val = (x.val * y.val) % 2^64
  rw [hv, Nat.mod_eq_of_lt h]

theorem sub_agree (x y : U32) (h : y.val ≤ x.val) :
    UScalar.sub x y = .ok (U32.wrapping_sub x y) := by
  obtain ⟨z, hz, hv⟩ := UnsignedReducerOps.sub_success x y h
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [U32.wrapping_sub_val_eq]
  have hs : UScalar.size .U32 = 2^32 := by simp [UScalar.size, U32.size, U32.numBits]
  rw [hs]
  change z.val = (x.val + (2^32 - y.val)) % 2^32
  have hx : x.val < 2^32 := x.bv.isLt
  have he : x.val + (2^32 - y.val) = (x.val - y.val) + 2^32 := by omega
  rw [hv, he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Negative control: agreement cannot be asserted without the subtraction
bound. The source bridge must not remove its premise to simplify a caller. -/
theorem sub_underflow_disagrees :
    UScalar.sub (0#u32) (1#u32) ≠ .ok (U32.wrapping_sub 0#u32 1#u32) := by
  rw [UnsignedReducerOps.sub_underflow _ _ (by simp)]
  simp

#print axioms add_agree
#print axioms mul_agree
#print axioms sub_agree
#print axioms sub_underflow_disagrees
end AspisV8R17.FullRuntimeWrapping
