import NMX_R3_ReferenceLength
set_option autoImplicit false
namespace NMX_R3_ByteCarrier
open Aeneas Aeneas.Std RSL

def byte (x : U8) : UInt8 := UInt8.ofNat x.val
def word (x : U32) : UInt32 := UInt32.ofNat x.val
def long (x : U64) : UInt64 := UInt64.ofNat x.val

theorem byte_value (x : U8) : (byte x).toNat = x.val :=
  UInt8.toNat_ofNat_of_lt' x.bv.isLt

theorem word_value (x : U32) : (word x).toNat = x.val :=
  UInt32.toNat_ofNat_of_lt' x.bv.isLt

theorem long_value (x : U64) : (long x).toNat = x.val :=
  UInt64.toNat_ofNat_of_lt' x.bv.isLt

theorem byte_injective : Function.Injective byte := by
  intro a b same
  apply UScalar.eq_of_val_eq
  have h := congrArg UInt8.toNat same
  simpa only [byte_value] using h

/-- Subwindows preserve exact byte arguments, including empty and truncated
windows; extent checks are handled separately at source call sites. -/
theorem window (xs : List U8) (i j : Nat) :
    slice (xs.map byte) i j = ((xs.drop i).take (j-i)).map byte := by
  simp only [slice, List.map_drop, List.map_take]
#print axioms byte_value
#print axioms word_value
#print axioms long_value
#print axioms byte_injective
#print axioms window
end NMX_R3_ByteCarrier
