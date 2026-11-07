import NMX_R3_ByteCarrier
set_option autoImplicit false
namespace NMX_R3_ByteCompare
open Aeneas Aeneas.Std NMX_R3_ByteCarrier

theorem equal (a b : U8) : byte a = byte b ↔ a = b :=
 ⟨fun same => byte_injective same, fun same => congrArg byte same⟩

theorem ne (a b : U8) : (a != b) = (byte a != byte b) := by
 change (!(a == b)) = (!(byte a == byte b))
 apply congrArg Bool.not
 apply Bool.eq_iff_iff.mpr
 simp only [beq_iff_eq, equal]

theorem le (a b : U8) : a ≤ b ↔ (byte a).toNat ≤ (byte b).toNat := by
 change a.val ≤ b.val ↔ (byte a).toNat ≤ (byte b).toNat
 rw [byte_value, byte_value]
#print axioms equal
#print axioms ne
#print axioms le
end NMX_R3_ByteCompare
