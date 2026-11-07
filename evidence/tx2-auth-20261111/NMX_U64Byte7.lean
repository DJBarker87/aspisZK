import NMX_U64Layout
set_option autoImplicit false
namespace NMX_U64Byte7
open Aeneas Aeneas.Std NMX_Carrier
/-- One symbolic emitted byte position, with no Scalar.val simplifier loop. -/
theorem value (x : U64) :
 (byte ((core.num.U64.to_le_bytes x).val.getD 7 0#u8)).toNat =
 x.val / 72057594037927936 % 256 := by
 rw [NMX_U64Layout.value]
 change (byte (⟨(((((((((((((((x.bv >>> 8).setWidth 56) >>> 8).setWidth 48) >>> 8).setWidth 40) >>> 8).setWidth 32) >>> 8).setWidth 24) >>> 8).setWidth 16) >>> 8).setWidth 8)).setWidth 8⟩ : U8)).toNat = x.bv.toNat / 72057594037927936 % 256
 rw [NMX_BvByte.low]
 have bound : x.bv.toNat < 18446744073709551616 := x.bv.isLt
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
 norm_num only [Nat.reducePow]
 omega
#print axioms value
end NMX_U64Byte7
