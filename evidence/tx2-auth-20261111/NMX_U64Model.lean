import NMX_ScalarCarrier
set_option autoImplicit false
namespace NMX_U64Model
open Aeneas Aeneas.Std NMX_Carrier
/-- Symbolic little-endian byte law for the canonical UInt64 carrier. -/
theorem value (x : U64) (i : Nat) (bound : i < 8) :
 ((long x >>> UInt64.ofNat (8*i)).toUInt8).toNat = x.val / 256^i % 256 := by
 have shiftBound : 8*i < 64 := by omega
 have scalarBound : 8*i < 18446744073709551616 := by omega
 have cast : (UInt64.ofNat (8*i)).toNat = 8*i := UInt64.toNat_ofNat_of_lt' scalarBound
 rw [UInt64.toNat_toUInt8,UInt64.toNat_shiftRight,NMX_ScalarCarrier.long_value,
  cast,Nat.mod_eq_of_lt shiftBound,Nat.shiftRight_eq_div_pow,Nat.pow_mul]
#print axioms value
end NMX_U64Model
