import NMX_InverseBytes
set_option autoImplicit false
namespace NMX_InverseSlice
open Aeneas Aeneas.Std NMX_Carrier NMX_InverseBytes
/-- Unrepresentable mathematical lists are explicit; no oversized runtime
buffer is allocated, copied, or silently truncated. -/
def fromBytes (b : RSL.Bytes) : Option (Slice U8) :=
 if size : b.length ≤ Usize.max then
  some ⟨b.map fromByte,by simpa using size⟩
 else none

theorem roundtrip (b : Slice U8) : fromBytes (bytes b) = some b := by
 unfold fromBytes
 have size : (bytes b).length ≤ Usize.max := by simpa only [bytes,List.length_map] using b.property
 rw [dif_pos size]
 apply congrArg some
 apply Subtype.ext
 simp [bytes,List.map_map,Function.comp_def,scalar_roundtrip]

#print axioms roundtrip
end NMX_InverseSlice
