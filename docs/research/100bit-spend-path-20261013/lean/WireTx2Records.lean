import WireTx2BinaryBodies
import WireBindingRecordCodec
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2.WireTx2
abbrev Bytes32 := Array U8 32#usize

def inputBytes (parts : Slice (Slice U8)) : List U8 := parts.val.flatMap Subtype.val

def singletonParts (s : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 1#usize [s])

def nodeParts (left right : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize
    [Array.to_slice (Array.make 1#usize [multiproof.BINARY_NODE_TAG]), left, right])

def checksumDomain : Slice U8 := Array.to_slice (Array.make 22#usize [
  85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8,
  58#u8, 82#u8, 49#u8, 58#u8, 99#u8, 104#u8, 101#u8,
  99#u8, 107#u8, 112#u8, 111#u8, 105#u8, 110#u8, 116#u8])

def checksumParts (body : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 2#usize [checksumDomain, body])

/-- The existing D79 classes, represented on the actual extracted byte type.
The checksum width alone is not authenticated checkpoint provenance. -/
inductive TypedInput : Slice (Slice U8) → Prop where
  | proof (s : Slice U8) (width : s.val.length = 57607) : TypedInput (singletonParts s)
  | publicAccount (s : Slice U8) (width : s.val.length = 1880) : TypedInput (singletonParts s)
  | checksum (s : Slice U8) (width : s.val.length = 1736) : TypedInput (checksumParts s)
  | node (left right : Slice U8) (hl : left.val.length = 32)
      (hr : right.val.length = 32) : TypedInput (nodeParts left right)
  | leaf (tag : U8) (values : Slice U8) (salt : Bytes32)
      (shape : (tag = 113#u8 ∧ values.val.length = 480) ∨
        ((tag = 241#u8 ∨ tag = 114#u8) ∧ values.val.length = 128)) :
      TypedInput (Array.to_slice (Array.make 3#usize [
        Array.to_slice (Array.make 2#usize [16#u8, tag]), values, Array.to_slice salt]))

theorem singleton_length (s : Slice U8) :
    (inputBytes (singletonParts s)).length = s.val.length := by
  change (s.val ++ []).length = s.val.length
  simp only [List.append_nil]

theorem node_length (l r : Slice U8) (hl : l.val.length = 32) (hr : r.val.length = 32) :
    (inputBytes (nodeParts l r)).length = 65 := by
  change ([multiproof.BINARY_NODE_TAG] ++ (l.val ++ (r.val ++ []))).length = 65
  simp only [List.length_append, List.length_cons, List.length_nil, hl, hr]

theorem checksum_length (body : Slice U8) (h : body.val.length = 1736) :
    (inputBytes (checksumParts body)).length = 1758 := by
  change (checksumDomain.val ++ (body.val ++ [])).length = 1758
  have hd : checksumDomain.val.length = 22 := rfl
  simp only [List.length_append, List.length_nil, hd, h]

/-- Every classified tx2 input has an already listed D79 class and its exact width. -/
theorem typed_class_length (parts : Slice (Slice U8)) (h : TypedInput parts) :
    ∃ c : AspisR1.WireBindingRecordCodec.Tx1Class,
      (inputBytes parts).length = c.size := by
  cases h with
  | proof s h => exact ⟨.binding .compactProof, by rw [singleton_length, h]; rfl⟩
  | publicAccount s h => exact ⟨.binding .asf8Account, by rw [singleton_length, h]; rfl⟩
  | checksum s h => exact ⟨.binding .checkpointChecksum, checksum_length s h⟩
  | node l r hl hr => exact ⟨.binaryNode, node_length l r hl hr⟩
  | leaf tag values salt shape =>
    have hs : salt.val.length = 32 := salt.property
    rcases shape with ⟨_, hv⟩ | ⟨_, hv⟩
    · refine ⟨.leafC1, ?_⟩
      change ([16#u8, tag] ++ (values.val ++ (salt.val ++ []))).length = 514
      simp only [List.length_append, List.length_cons, List.length_nil, hs, hv]
    · refine ⟨.leafSmall, ?_⟩
      change ([16#u8, tag] ++ (values.val ++ (salt.val ++ []))).length = 162
      simp only [List.length_append, List.length_cons, List.length_nil, hs, hv]

#print axioms singleton_length
#print axioms node_length
#print axioms checksum_length
#print axioms typed_class_length
end AspisR1Stage2.WireTx2
