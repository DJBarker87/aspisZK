import R1Z.PV_CB3_WeightsMachine
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsCount
open Aeneas Aeneas.Std

def count (d : Usize) : U32 := UScalar.cast .U32 (Usize.wrapping_mul 2#usize d)

theorem product_value (d : Usize) (hd : d.val < 5) :
    (Usize.wrapping_mul 2#usize d).val = 2*d.val := by
  change ((2#usize).bv*d.bv).toNat = _
  rw [BitVec.toNat_mul]
  change (2*d.val)%2^(UScalarTy.numBits .Usize) = 2*d.val
  apply Nat.mod_eq_of_lt
  have hw := PV_CB3_WeightsMachine.width_min
  have hp : 2^10 ≤ 2^(UScalarTy.numBits .Usize) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem value (d : Usize) (hd : d.val < 5) : (count d).val = 2*d.val := by
  unfold count
  rw [PV_CB3_WeightsMachine.cast_count _ (by rw [product_value d hd]; omega),product_value d hd]

theorem bound (d : Usize) (hd : d.val < 5) : (count d).val < 10 := by
  rw [value d hd]
  omega
#print axioms product_value
#print axioms value
#print axioms bound
end R1Z.PV_CB3_WeightsCount
