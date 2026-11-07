import NMX_R3_ByteCarrier
set_option autoImplicit false
namespace NMX_R3_Bits
open Aeneas Aeneas.Std NMX_R3_ByteCarrier
/-- Symbolic wrappers, without any recurrence or large numeral reduction. -/
theorem byte_bits (x : U8) : (byte x).toBitVec = x.bv := by
  change BitVec.ofNat 8 x.bv.toNat = x.bv
  simpa using BitVec.ofNat_toNat 8 x.bv

theorem word_bits (x : U32) : (word x).toBitVec = x.bv := by
  change BitVec.ofNat 32 x.bv.toNat = x.bv
  simpa using BitVec.ofNat_toNat 32 x.bv
#print axioms byte_bits
#print axioms word_bits
end NMX_R3_Bits
#print UInt8.toUInt32
#print UInt32.lor
#print UInt32.shiftLeft
#print BitVec.fromLEBytes
