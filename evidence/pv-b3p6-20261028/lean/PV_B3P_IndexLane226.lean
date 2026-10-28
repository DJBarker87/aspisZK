import PV_B3P_ScalarRegions226
import PV_B3P_EndianVerified226V3
namespace PV_B3P_IndexLane226
open Aeneas Aeneas.Std PV_B3P_ByteLayout226V3
set_option autoImplicit false

theorem shift_value (j : Usize) (hj : j.val < 8) :
    (U32.wrapping_mul 8#u32 (UScalar.cast .U32 j)).val = 8*j.val := by
  rw [U32.wrapping_mul_val_eq,UScalar.cast_val_eq]
  norm_num [UScalar.size,UScalarTy.numBits,U32.size,U32.numBits]
  omega

set_option backward.isDefEq.respectTransparency false in
theorem native_value (v : U64) (j : Usize) (hj : j.val < 8) :
    PV_B3P_ScalarRegions226.indexLane v j =
      (core.num.U64.to_le_bytes v).val[j.val]'(by
        rw [(core.num.U64.to_le_bytes v).property]; simpa using hj) := by
  unfold PV_B3P_ScalarRegions226.indexLane
  simp only [core.num.U64.to_le_bytes,List.getElem_map]
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  change (U64.wrapping_shr v (U32.wrapping_mul 8#u32 (UScalar.cast .U32 j))).bv.toNat % (2 ^ UScalarTy.U8.numBits) =
    (v.bv.toLEBytes[j.val]'(by rw [BitVec.toLEBytes_length]; simpa only [UScalarTy.numBits] using hj)).toNat
  norm_num only [UScalarTy.numBits] at *
  rw [U64.wrapping_shr_bv_eq,shift_value j hj]
  have hm : (8*j.val)%64 = 8*j.val := Nat.mod_eq_of_lt (by omega)
  simp only [UScalarTy.numBits,hm,BitVec.toNat_ushiftRight]
  exact (PV_B3P_EndianVerified226V3.lane_nat v.bv j.val (by simpa only [UScalarTy.numBits] using (show 8*j.val+8 ≤ 64 by omega))
    (by rw [BitVec.toLEBytes_length]; simpa only [UScalarTy.numBits] using hj)).symm

#print axioms shift_value
#print axioms native_value
end PV_B3P_IndexLane226
