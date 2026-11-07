import NMX_R2_KeyCarrier
set_option autoImplicit false
namespace NMX_R2_InverseBytes
open Aeneas Aeneas.Std NMX_R2_Carrier NMX_R2_ScalarCarrier

def fromByte (b : UInt8) : U8 :=
 UScalar.ofNatCore b.toNat (UInt8.toNat_lt b)
def fromKey (k : RSL.B32) : Array U8 32#usize :=
 ⟨k.bytes.map fromByte,by simpa using k.len⟩

theorem byte_roundtrip (b : UInt8) : byte (fromByte b) = b := by
 simp [fromByte,byte,UScalar.ofNatCore_val_eq]

theorem scalar_roundtrip (b : U8) : fromByte (byte b) = b := by
 apply UScalar.eq_of_val_eq
 simp only [fromByte,UScalar.ofNatCore_val_eq,byte_value]

theorem b32_ext (a b : RSL.B32) (same : a.bytes = b.bytes) : a = b := by
 cases a
 cases b
 cases same
 rfl

theorem key_roundtrip (k : RSL.B32) : key (fromKey k) = k := by
 apply b32_ext
 simp [key,fromKey,List.map_map,Function.comp_def,byte_roundtrip]

theorem array_roundtrip (k : Array U8 32#usize) : fromKey (key k) = k := by
 apply Subtype.ext
 simp [fromKey,key,List.map_map,Function.comp_def,scalar_roundtrip]
#print axioms byte_roundtrip
#print axioms scalar_roundtrip
#print axioms b32_ext
#print axioms key_roundtrip
#print axioms array_roundtrip
end NMX_R2_InverseBytes
