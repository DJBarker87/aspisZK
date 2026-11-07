import NMX_R3_Bits
set_option autoImplicit false
namespace NMX_R3_ByteWord
open Aeneas Aeneas.Std NMX_R3_ByteCarrier
/-- Widening a byte does not change its unsigned value. -/
theorem bits (x : U8) : (byte x).toUInt32.toBitVec = x.bv.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  change (byte x).toNat = (x.bv.setWidth 32).toNat
  rw [NMX_R3_ByteCarrier.byte_value, BitVec.toNat_setWidth]
  change x.bv.toNat = x.bv.toNat % 4294967296
  have bound := x.bv.isLt
  exact (Nat.mod_eq_of_lt (by omega)).symm
#print axioms bits
end NMX_R3_ByteWord
