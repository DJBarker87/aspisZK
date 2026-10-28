import R1Z.PV_Src_ExternalReduce
import AspisV8R17.RawReducerNat

/-! The release reducer's folds remain in U64. Bounds are symbolic for all
raw U64 inputs; no concrete recurrence term is normalized. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ScalarFold
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open AspisV8R17.RawReducer

def mask : U64 := UScalar.cast .U64 (2147483647#u32 : U32)
def fold (x : U64) : U64 := U64.wrapping_add (x &&& mask) (U64.wrapping_shr x 31#u32)

theorem mask_value : mask.val = 2147483647 := by rw [mask,c64]; rfl

theorem shift_value (x : U64) : (U64.wrapping_shr x 31#u32).val = x.val >>> 31 := by
  change (U64.wrapping_shr x 31#u32).bv.toNat = _
  rw [U64.wrapping_shr_bv_eq]
  change (x.bv.ushiftRight 31).toNat = _
  exact BitVec.toNat_ushiftRight _ _

theorem fold_value (x : U64) : (fold x).val = foldBits x.val := by
  have hand : (x &&& mask).val = x.val &&& 2147483647 := by rw [UScalar.val_and,mask_value]
  have bound := first_fold_lt x.val x.bv.isLt
  unfold fold
  exact add64v _ _ _ _ hand (shift_value x) (by change foldBits x.val < 18446744073709551616; omega)

theorem narrow_value (x : U64) :
    (UScalar.cast .U32 (fold (fold x))).val = foldBits (foldBits x.val) := by
  have hv : (fold (fold x)).val = foldBits (foldBits x.val) := by rw [fold_value,fold_value]
  rw [c32 _ (by rw [hv]; exact second_fold_lt_two_pow32 x.val x.bv.isLt),hv]

#print axioms mask_value
#print axioms shift_value
#print axioms fold_value
#print axioms narrow_value
end R1Z.PV_Src_ScalarFold
