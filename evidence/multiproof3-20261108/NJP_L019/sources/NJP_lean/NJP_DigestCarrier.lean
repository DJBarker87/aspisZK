import NJP_RowModel
import MultiproofConeNodeAdoption

set_option autoImplicit false
noncomputable section
namespace NJP_DigestCarrier
open Aeneas Aeneas.Std Result NJP_RowModel
abbrev RefDigest := Array U8 32#usize

def encode (bytes : Digest) : RefDigest := ⟨List.ofFn bytes,by simp⟩
def decode (bytes : RefDigest) (j : Fin 32) : U8 :=
 bytes.val[j.val]'(by have size := bytes.property;change bytes.val.length=32 at size;omega)

theorem coordinate (bytes : Digest) (j : Fin 32) : decode (encode bytes) j=bytes j := by
 simp only [decode,encode,List.getElem_ofFn]

theorem decode_encode (bytes : Digest) : decode (encode bytes)=bytes := funext (coordinate bytes)

theorem encode_decode (bytes : RefDigest) : encode (decode bytes)=bytes := by
 apply AspisR1.MultiproofConeNodeAdoption.array_ext
 intro j left right
 simp only [encode,List.getElem_ofFn,decode]

theorem faithful (left right : RefDigest) (same : decode left=decode right) : left=right := by
 rw [←encode_decode left,←encode_decode right,same]

/-- Full 16-digest array: the source G carrier retains every inactive byte. -/
def encodeValues (values : Fin 16 → Digest) : Array RefDigest 16#usize :=
 ⟨List.ofFn (fun i => encode (values i)),by simp⟩

def decodeValues (values : Array RefDigest 16#usize) (i : Fin 16) : Digest :=
 decode (values.val[i.val]'(by have size := values.property;change values.val.length=16 at size;omega))

theorem values_coordinate (values : Fin 16 → Digest) (i : Fin 16) :
 decodeValues (encodeValues values) i=values i := by
 simp only [decodeValues,encodeValues,List.getElem_ofFn,decode_encode]

theorem values_roundtrip (values : Array RefDigest 16#usize) : encodeValues (decodeValues values)=values := by
 apply AspisR1.MultiproofConeNodeAdoption.array_ext
 intro j left right
 simp only [encodeValues,List.getElem_ofFn,decodeValues,encode_decode]

#print coordinate
#print axioms coordinate
#print decode_encode
#print axioms decode_encode
#print encode_decode
#print axioms encode_decode
#print faithful
#print axioms faithful
#print values_coordinate
#print axioms values_coordinate
#print values_roundtrip
#print axioms values_roundtrip
end NJP_DigestCarrier
end
