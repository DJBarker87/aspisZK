import AspisR1ProverLeaf.Funs
import R1Z.SharedGrammarBridgeBin
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.ProverCommitLeafSource
open AspisR1ProverLeaf
abbrev Bytes32 := Aeneas.Std.Array U8 32#usize

def leafSlices (tag : U8) (value : Slice U8) (salt : Bytes32) : Slice (Slice U8) :=
  Aeneas.Std.Array.to_slice (Aeneas.Std.Array.make 3#usize [
    Aeneas.Std.Array.to_slice (Aeneas.Std.Array.make 2#usize [16#u8,tag]),
    value, Aeneas.Std.Array.to_slice salt])

def byte (x : U8) : UInt8 := x.val.toUInt8

def wireBytes (s : Slice (Slice U8)) : List UInt8 :=
  (s.val.flatMap (fun x => x.val)).map byte

def tagOf (tree : Fin 3) : U8 :=
  if tree.val = 0 then 113#u8 else if tree.val = 1 then 241#u8 else 114#u8

/-- The actual generic private-leaf function delegates precisely these three
slices to any supplied callback. No hash or field law is assumed. -/
theorem leaf_source
    (hash : Slice (Slice U8) → Result Bytes32) (tag : U8)
    (value : Slice U8) (salt : Bytes32) :
    state_only_private_merkle.private_leaf_hash hash tag value salt =
      hash (leafSlices tag value salt) := by
  simp [state_only_private_merkle.private_leaf_hash,
    state_only_private_merkle.private_leaf_hash_with_digest,
    digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32,
    digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest,
    state_only_private_merkle.DOM_LEAF, leafSlices, lift]

/-- Concrete tags transported to D81's shared binary grammar. -/
theorem tag_eq (tree : Fin 3) :
    byte (tagOf tree) = AspisR1.SharedBinaryRecordGrammar.treeTag tree := by
  unfold tagOf AspisR1.SharedBinaryRecordGrammar.treeTag
  split_ifs <;> rfl

/-- Flattening the extracted callback gives the shared grammar, with the
value bytes untouched and the full salt trailing. Packed-value provenance
from the actual tree caller is a separate refinement. -/
theorem leaf_shared (tree : Fin 3) (value : Slice U8) (salt : Bytes32) :
    wireBytes (leafSlices (tagOf tree) value salt) =
      AspisR1.SharedBinaryRecordGrammar.leafInput
        (AspisR1.SharedBinaryRecordGrammar.treeTag tree)
        (value.val.map byte) (salt.val.map byte) := by
  simp [wireBytes, leafSlices, Aeneas.Std.Array.to_slice, Aeneas.Std.Array.make,
    AspisR1.SharedBinaryRecordGrammar.leafInput, byte, tagOf,
    AspisR1.SharedBinaryRecordGrammar.treeTag, List.map_append, List.append_assoc]
  split_ifs <;> rfl

#print axioms leaf_source
#print axioms tag_eq
#print axioms leaf_shared
end R1Z.ProverCommitLeafSource
