import NMX_R3_ByteCarrier
set_option autoImplicit false
namespace NMX_R3_LongBits
open Aeneas Aeneas.Std NMX_R3_ByteCarrier

theorem value (x : U64) : (long x).toBitVec = x.bv := by
 change BitVec.ofNat 64 x.bv.toNat = x.bv
 simpa using BitVec.ofNat_toNat 64 x.bv

theorem byte_widen (x : U8) : (byte x).toUInt64 = (⟨x.bv.setWidth 64⟩ : UInt64) := by
 apply UInt64.toBitVec_inj.mp
 apply BitVec.eq_of_toNat_eq
 change (byte x).toNat = (x.bv.setWidth 64).toNat
 rw [byte_value, BitVec.toNat_setWidth]
 change x.bv.toNat = x.bv.toNat % 18446744073709551616
 have bound := x.bv.isLt
 exact (Nat.mod_eq_of_lt (by omega)).symm

theorem injective : Function.Injective long := by
 intro a b same
 apply UScalar.eq_of_val_eq
 have h := congrArg UInt64.toNat same
 simpa only [long_value] using h
#print axioms value
#print axioms byte_widen
#print axioms injective
end NMX_R3_LongBits
