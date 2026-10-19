import RawMerkleParentCall
import R1Merkle32Path

/-! Literal 257-byte preimage of the emitted current Merkle parent helper.
The source parent helper itself is unchanged in the explicit-child candidate.
No hash ideality, collision exclusion, or accepted-path premise is assumed. -/
set_option autoImplicit false
namespace AspisR1MerklePathChildren.RawMerkleParentBytes
open Aeneas Aeneas.Std Result
open RawMerkleParentCall

def decodeByte (b : U8) : AspisR1.Merkle32Path.Byte := ⟨b.val, b.bv.isLt⟩
def decodeDigest (d : Digest) : AspisR1.Merkle32Path.Digest :=
  fun i => decodeByte (d.val[i.val]'(by simpa [d.property] using i.isLt))
def decodeChildren (children : Children) : AspisR1.Merkle32Path.Children :=
  fun i => decodeDigest (child children i)
def flattenParts (parts : Slice (Slice U8)) : List AspisR1.Merkle32Path.Byte :=
  (parts.val.flatMap (fun part => part.val)).map decodeByte

theorem digest_bytes (d : Digest) :
    List.ofFn (decodeDigest d) = d.val.map decodeByte := by
  apply List.ext_getElem
  · simp [d.property]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, decodeDigest]

/-- Split only the eight outer children; the 32 bytes remain symbolic. -/
theorem nodeBytes_children (children : AspisR1.Merkle32Path.Children) :
    AspisR1.Merkle32Path.nodeBytes children = (List.ofFn (fun i : Fin 8 => List.ofFn (children i))).flatten := by
  unfold AspisR1.Merkle32Path.nodeBytes
  rw [List.ofFn_mul (m := 8) (n := 32)]
  congr 1

private theorem ofFn8 {α : Type} (f : Fin 8 → α) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := by rfl

/-- The nine grouped source arguments flatten to exactly 0x18 followed by the
8x32 child-major bytes consumed by the existing Merkle32 path theorem. -/
theorem parent_literal_bytes (children : Children) :
    flattenParts (parentParts children) = AspisR1.Merkle32Path.nodeInput (decodeChildren children) := by
  rw [AspisR1.Merkle32Path.nodeInput, nodeBytes_children, ofFn8]
  simp only [decodeChildren, digest_bytes]
  simp [flattenParts, parentParts, Array.to_slice, Array.make, List.map_append, decodeByte]

#print axioms digest_bytes
#print axioms nodeBytes_children
#print axioms parent_literal_bytes
end AspisR1MerklePathChildren.RawMerkleParentBytes
