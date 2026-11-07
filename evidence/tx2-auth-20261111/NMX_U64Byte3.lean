import NMX_BvByte
set_option autoImplicit false
namespace NMX_U64Byte3
open Aeneas Aeneas.Std NMX_Carrier
/-- One symbolic emitted byte position, with no Scalar.val simplifier loop. -/
theorem value (x : U64) :
 (byte ((core.num.U64.to_le_bytes x).val.getD 3 0#u8)).toNat =
 x.val / 16777216 % 256 := by
 change (byte (⟨(((((((x.bv >>> 8).setWidth 56) >>> 8).setWidth 48) >>> 8).setWidth 40)).setWidth 8⟩ : U8)).toNat = x.bv.toNat / 16777216 % 256
 rw [NMX_BvByte.low]
 have bound : x.bv.toNat < 18446744073709551616 := x.bv.isLt
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
 norm_num only [Nat.reducePow]
 omega
#print axioms value
end NMX_U64Byte3
