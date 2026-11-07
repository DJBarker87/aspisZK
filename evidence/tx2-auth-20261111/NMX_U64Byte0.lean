import NMX_BvByte
set_option autoImplicit false
namespace NMX_U64Byte0
open Aeneas Aeneas.Std NMX_Carrier
/-- One symbolic emitted byte position, with no Scalar.val simplifier loop. -/
theorem value (x : U64) :
 (byte ((core.num.U64.to_le_bytes x).val.getD 0 0#u8)).toNat =
 x.val / 1 % 256 := by
 change (byte (⟨(x.bv).setWidth 8⟩ : U8)).toNat = x.bv.toNat / 1 % 256
 rw [NMX_BvByte.low,Nat.div_one]
#print axioms value
end NMX_U64Byte0
