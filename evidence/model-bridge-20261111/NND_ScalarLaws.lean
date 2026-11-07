import NND_Carrier
set_option autoImplicit false
namespace NND_Carrier
open Aeneas Aeneas.Std

theorem byte_and (x y : U8) : byte (x &&& y) = byte x &&& byte y := rfl
theorem byte_zero : byte 0#u8 = (0 : UInt8) := rfl
theorem slot_le (x y : U64) : (x ≤ y) ↔ (slot x ≤ slot y) := Iff.rfl
theorem slot_lt (x y : U64) : (x < y) ↔ (slot x < slot y) := Iff.rfl
theorem word_lt (x y : U32) : (x < y) ↔ (word x < word y) := Iff.rfl
theorem slot_max : slot 18446744073709551615#u64 = (0xffffffffffffffff : UInt64) := rfl
theorem byte_injective : Function.Injective byte := by
 intro x y h
 exact (byte_back x).symm.trans ((congrArg unbyte h).trans (byte_back y))
theorem key_injective : Function.Injective key := by
 intro x y h
 exact (key_back x).symm.trans ((congrArg unkey h).trans (key_back y))
#print axioms byte_and
#print axioms byte_zero
#print axioms slot_le
#print axioms slot_lt
#print axioms word_lt
#print axioms slot_max
#print axioms byte_injective
#print axioms key_injective
end NND_Carrier
