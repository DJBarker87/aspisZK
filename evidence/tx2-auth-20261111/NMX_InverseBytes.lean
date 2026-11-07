import NMX_KeyCarrier
set_option autoImplicit false
namespace NMX_InverseBytes
open Aeneas Aeneas.Std NMX_Carrier NMX_ScalarCarrier

def fromByte (b : UInt8) : U8 :=
 UScalar.ofNatCore b.toNat (UInt8.toNat_lt b)
def fromKey (k : RSL.B32) : Array U8 32#usize :=
 ⟨k.bytes.map fromByte,by simpa using k.len⟩

theorem byte_roundtrip (b : UInt8) : byte (fromByte b) = b := by
 simp [fromByte,byte,UScalar.ofNatCore_val_eq]

theorem scalar_roundtrip (b : U8) : fromByte (byte b) = b := by
 apply UScalar.eq_of_val_eq
 simp only [fromByte,UScalar.ofNatCore_val_eq,byte_value]

theorem key_roundtrip (k : RSL.B32) : key (fromKey k) = k := by
 cases k with
 | mk values size =>
   apply RSL.B32.mk.injEq.mpr
   simp only [key,fromKey,List.map_map]
   have identity : (fun b => byte (fromByte b)) = id := funext byte_roundtrip
   rw [identity,List.map_id]

theorem array_roundtrip (k : Array U8 32#usize) : fromKey (key k) = k := by
 apply Subtype.ext
 simp only [fromKey,key,List.map_map]
 have identity : (fun b => fromByte (byte b)) = id := funext scalar_roundtrip
 rw [identity,List.map_id]
#print axioms byte_roundtrip
#print axioms scalar_roundtrip
#print axioms key_roundtrip
#print axioms array_roundtrip
end NMX_InverseBytes
