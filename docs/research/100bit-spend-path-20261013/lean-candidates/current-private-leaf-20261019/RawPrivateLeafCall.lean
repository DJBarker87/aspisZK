import AspisR1PrivateLeaf.Funs
import RawMerkleParentBytes
import R1Merkle32Leaf

/-! Literal private leaf input for the unchanged source helper. -/
set_option autoImplicit false
namespace AspisR1PrivateLeaf.RawPrivateLeafCall
open Aeneas Aeneas.Std Result
open AspisR1MerklePathChildren.RawMerkleParentBytes (decodeByte decodeDigest flattenParts)
abbrev Digest := Array U8 32#usize

def leafParts (tag : U8) (value : Slice U8) (salt : Digest) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize
    [Array.to_slice (Array.make 2#usize [16#u8,tag]),value,Array.to_slice salt])

theorem leaf_equation {H : Type} (D : Digest32 H) (hash : H)
    (tag : U8) (value : Slice U8) (salt : Digest) :
    state_only_private_merkle.private_leaf_hash_with_digest D hash tag value salt =
      D.digest hash (leafParts tag value salt) := by
  simp only [state_only_private_merkle.private_leaf_hash_with_digest,
    state_only_private_merkle.DOM_LEAF,lift,bind_tc_ok]
  rfl

theorem leaf_literal_bytes (tag : U8) (value : Slice U8) (salt : Digest) :
    flattenParts (leafParts tag value salt) =
      AspisR1.Merkle32Leaf.leafInput (decodeByte tag)
        (value.val.map decodeByte) (salt.val.map decodeByte) := by
  simp [flattenParts,leafParts,Array.to_slice,Array.make,
    AspisR1.Merkle32Leaf.leafInput,decodeByte]

theorem salt_width (salt : Digest) : (salt.val.map decodeByte).length = 32 := by
  simpa using salt.property

theorem successful_leaf_global {H : Type} (D : Digest32 H) (hash : H)
    (tag : U8) (value : Slice U8) (salt node : Digest)
    (h : state_only_private_merkle.private_leaf_hash_with_digest D hash tag value salt = ok node)
    (oracle : List (Fin 256) → AspisR1.Merkle32Path.Digest)
    (tr : List (List (Fin 256) × AspisR1.Merkle32Path.Digest))
    (hread : (flattenParts (leafParts tag value salt),decodeDigest node) ∈ tr)
    (hglobal : ∀ q ∈ tr, q.2 = oracle q.1) :
    D.digest hash (leafParts tag value salt) = ok node ∧
    decodeDigest node = oracle (AspisR1.Merkle32Leaf.leafInput
      (decodeByte tag) (value.val.map decodeByte) (salt.val.map decodeByte)) := by
  refine ⟨?_,?_⟩
  · rwa [← leaf_equation]
  · simpa only [leaf_literal_bytes] using hglobal _ hread

#print axioms leaf_equation
#print axioms leaf_literal_bytes
#print axioms salt_width
#print axioms successful_leaf_global
end AspisR1PrivateLeaf.RawPrivateLeafCall
