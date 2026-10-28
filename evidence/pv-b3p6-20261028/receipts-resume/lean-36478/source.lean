import PV_B3P_ScalarRegions226
import PV_B3P_EndianVerified226V3
namespace PV_B3P_IndexLane226
open Aeneas Aeneas.Std PV_B3P_ByteLayout226V3
set_option autoImplicit false

theorem shift_value (j : Usize) (hj : j.val < 8) :
    (U32.wrapping_mul 8#u32 (UScalar.cast .U32 j)).val = 8*j.val := by
  rw [U32.wrapping_mul_val_eq,UScalar.cast_val_eq]
  change (8*(j.val%4294967296))%4294967296 = 8*j.val
  rw [Nat.mod_eq_of_lt (show j.val < 4294967296 by omega),
    Nat.mod_eq_of_lt (show 8*j.val < 4294967296 by omega)]

set_option backward.isDefEq.respectTransparency false in
theorem native_value (v : U64) (j : Usize) (hj : j.val < 8) :
    PV_B3P_ScalarRegions226.indexLane v j =
      (core.num.U64.to_le_bytes v).val[j.val]'(by
        rw [(core.num.U64.to_le_bytes v).property]; simpa using hj) := by
  unfold PV_B3P_ScalarRegions226.indexLane
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  change (U64.wrapping_shr v (U32.wrapping_mul 8#u32 (UScalar.cast .U32 j))).bv.toNat % 256 =
    (v.bv.toLEBytes[j.val]'(by rw [BitVec.toLEBytes_length]; scalar_tac)).toNat
  rw [U64.wrapping_shr_bv_eq,shift_value j hj]
  have hm : (8*j.val)%64 = 8*j.val := Nat.mod_eq_of_lt (by omega)
  simp only [hm,BitVec.toNat_ushiftRight]
  exact (PV_B3P_EndianVerified226V3.lane_nat v.bv j.val (by omega)
    (by rw [BitVec.toLEBytes_length]; scalar_tac)).symm

#print axioms shift_value
#print axioms native_value
end PV_B3P_IndexLane226
