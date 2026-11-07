import PCF_LaneShape
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCF_LaneValue

theorem low_lane (a : U32) : (PCF_LaneShape.lowLane a).val = a.val % 8 := by
  unfold PCF_LaneShape.lowLane
  rw [UScalar.cast_val_eq]
  have hv : ((UScalar.cast .U8 a) &&& 7#u8).val = (a.val % 256) &&& 7 := by
    change ((UScalar.cast .U8 a).bv &&& (7#u8).bv).toNat = _
    rw [BitVec.toNat_and]
    simp only [UScalar.bv_toNat, UScalar.cast_val_eq]
    rfl
  rw [hv]
  have hm : (a.val % 256) &&& 7 = a.val % 8 := by
    have h := Nat.and_two_pow_sub_one_eq_mod (a.val % 256) 3
    change (a.val % 256) &&& 7 = (a.val % 256) % 8 at h
    rw [h]
    omega
  rw [hm]
  have small : a.val % 8 < 8 := Nat.mod_lt _ (by decide)
  change a.val % 8 % 65536 = a.val % 8
  exact Nat.mod_eq_of_lt (by omega)

#print axioms low_lane
end PCF_LaneValue
