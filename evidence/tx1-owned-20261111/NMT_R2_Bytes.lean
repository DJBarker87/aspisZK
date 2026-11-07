import NMT_345RSLCarriers
import NMT_R2_Base
set_option autoImplicit false
noncomputable section
namespace NMT_R2_Bytes
open Aeneas Aeneas.Std NMT_345 RSL
/-- Canonical bytes have a total inverse as emitted U8 values. -/
def unbyte (b : UInt8) : U8 := ⟨b.toNat,by have h := b.toNat_lt; omega⟩
theorem byte_unbyte (b : UInt8) : byte (unbyte b) = b := by
 change UInt8.ofNat b.toNat = b
 exact UInt8.ofNat_toNat

theorem unbyte_byte (b : U8) : unbyte (byte b) = b := by
 apply UScalar.eq_of_val_eq
 exact byte_nat b

def native (bytes : Bytes) : List U8 := bytes.map unbyte

theorem bytes_native (bytes : Bytes) : (native bytes).map byte = bytes := by
 simp only [native,List.map_map,Function.comp_def,byte_unbyte]
 induction bytes <;> simp_all

theorem native_bytes (bytes : List U8) : native (bytes.map byte) = bytes := by
 simp only [native,List.map_map,Function.comp_def,unbyte_byte]
 induction bytes <;> simp_all
#print axioms byte_unbyte
#print axioms unbyte_byte
#print axioms bytes_native
#print axioms native_bytes
end NMT_R2_Bytes
end
