import Aeneas
set_option autoImplicit false
namespace R1Z.PV_CB3_MaskCast
open Aeneas Aeneas.Std

def low (row : Usize) : Usize := row &&& 15#usize

theorem low_value (row : Usize) : (low row).val = (row.val &&& 15) := by
  change (row.bv &&& (15#usize).bv).toNat = _
  rw [BitVec.toNat_and]
  rfl

theorem low_bound (row : Usize) : (low row).val < 16 := by
  rw [low_value]
  have h : row.val &&& 15 ≤ 15 := Nat.and_le_right
  omega

/-- The only added shift-count cast in the compatibility adapter is exact. -/
theorem cast_value (row : Usize) :
    (UScalar.cast .U32 (low row)).val = (low row).val := by
  change (BitVec.zeroExtend 32 (low row).bv).toNat = _
  rw [BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth]
  apply Nat.mod_eq_of_lt
  have h := low_bound row
  change (low row).val < 4294967296
  omega

theorem literal_four : (4#i32).val = ((4#u32).val : Int) := rfl
#print axioms low_value
#print axioms low_bound
#print axioms cast_value
#print axioms literal_four
end R1Z.PV_CB3_MaskCast
