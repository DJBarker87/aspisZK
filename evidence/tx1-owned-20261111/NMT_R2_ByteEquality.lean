import NMT_345RSLCarriers
set_option autoImplicit false
namespace NMT_R2_ByteEquality
open Aeneas Aeneas.Std NMT_345

theorem byte_equal (a b : U8) : (byte a == byte b) = (a == b) := by
 have he : byte a = byte b ↔ a = b := ⟨fun h => byte_injective h,fun h => congrArg byte h⟩
 apply Bool.eq_iff_iff.mpr
 simpa [Aeneas.Std.instBEqUScalar_1] using he

theorem zeros (bytes : List U8) :
 (bytes.map byte).all (· == 0) = bytes.all (· == 0#u8) := by
 induction bytes with
 | nil => rfl
 | cons b rest ih =>
  simp only [List.map_cons,List.all_cons,ih]
  have h := byte_equal b 0#u8
  exact congrArg (fun x => x && rest.all (· == 0#u8)) h
#print axioms byte_equal
#print axioms zeros
end NMT_R2_ByteEquality
