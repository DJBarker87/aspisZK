import NND_Carrier
set_option autoImplicit false
namespace PCM_Bytes
open Aeneas Aeneas.Std
abbrev bytes := NND_Carrier.bytes
def rawBytes (bs : RSL.Bytes) : List U8 := bs.map NND_Carrier.unbyte

def fromBytes (bs : RSL.Bytes) (h : bs.length ≤ Usize.max) : Slice U8 :=
  ⟨rawBytes bs,by simpa [rawBytes] using h⟩

theorem from_bytes (b : Slice U8) (h : (bytes b).length ≤ Usize.max) :
    fromBytes (bytes b) h = b := by
  apply Subtype.ext
  simp [fromBytes,rawBytes,bytes,NND_Carrier.bytes,List.map_map,Function.comp_def]

theorem bytes_from (bs : RSL.Bytes) (h : bs.length ≤ Usize.max) :
    bytes (fromBytes bs h) = bs := by
  simp [bytes,fromBytes,NND_Carrier.bytes,rawBytes,List.map_map,Function.comp_def]

theorem bytes_bound (b : Slice U8) : (bytes b).length ≤ Usize.max := by
  simpa [bytes,NND_Carrier.bytes] using b.property

#print axioms from_bytes
#print axioms bytes_from
#print axioms bytes_bound
end PCM_Bytes
