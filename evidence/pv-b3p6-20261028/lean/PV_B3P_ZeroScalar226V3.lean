import PV_B3P_ByteScalar226V3
namespace PV_B3P_ZeroScalar226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteScalar226V3
set_option autoImplicit false

theorem shift_zero (q : U32) : U32.wrapping_shr 0#u32 q = 0#u32 := by
  apply UScalar.eq_of_val_eq
  change (U32.wrapping_shr 0#u32 q).bv.toNat = 0
  rw [U32.wrapping_shr_bv_eq]
  simp [BitVec.toNat_ushiftRight]

theorem field_zero (j : Usize) : reference226.field_byte 0#u32 j = .ok (.Ok 0#u8) := by
  have hc : (0#u32) < 2147483647#u32 := by decide
  rw [field_success 0#u32 j hc,shift_zero]
  rfl

#print axioms shift_zero
#print axioms field_zero
end PV_B3P_ZeroScalar226V3
