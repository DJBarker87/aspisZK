import NMX_ScalarCarrier
set_option autoImplicit false
namespace NMX_ScalarBne
open Aeneas Aeneas.Std NMX_Carrier NMX_ScalarCarrier

theorem byte_equal (a b : U8) : byte a = byte b ↔ a = b :=
 ⟨fun same => byte_injective same,fun same => congrArg byte same⟩

theorem byte_ne (a b : U8) : (a != b) = (byte a != byte b) := by
 change (!(a == b)) = (!(byte a == byte b))
 apply congrArg Bool.not
 apply Bool.eq_iff_iff.mpr
 simp only [beq_iff_eq,byte_equal]

theorem mask : byte 255#u8 = RSL.ALL_LANES_MASK := rfl
#print axioms byte_equal
#print axioms byte_ne
#print axioms mask
end NMX_ScalarBne
