import NMX_R2_Carrier
set_option autoImplicit false
namespace NMX_R2_ScalarCarrier
open Aeneas Aeneas.Std NMX_R2_Carrier

theorem byte_value (x : U8) : (byte x).toNat = x.val := by
 exact UInt8.toNat_ofNat_of_lt' x.bv.isLt

theorem word_value (x : U32) : (word x).toNat = x.val := by
 exact UInt32.toNat_ofNat_of_lt' x.bv.isLt

theorem long_value (x : U64) : (long x).toNat = x.val := by
 exact UInt64.toNat_ofNat_of_lt' x.bv.isLt

theorem byte_injective : Function.Injective byte := by
 intro a b same
 apply UScalar.eq_of_val_eq
 have h := congrArg UInt8.toNat same
 simpa only [byte_value] using h

theorem long_injective : Function.Injective long := by
 intro a b same
 apply UScalar.eq_of_val_eq
 have h := congrArg UInt64.toNat same
 simpa only [long_value] using h
#print axioms byte_value
#print axioms word_value
#print axioms long_value
#print axioms byte_injective
#print axioms long_injective
end NMX_R2_ScalarCarrier
