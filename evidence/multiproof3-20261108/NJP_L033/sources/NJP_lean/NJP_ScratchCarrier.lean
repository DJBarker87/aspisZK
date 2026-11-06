import NJP_ScalarCarrier

set_option autoImplicit false
noncomputable section
namespace NJP_ScratchCarrier
open Aeneas Aeneas.Std Result NJP_RowModel NJP_DigestCarrier NJP_ScalarCarrier
open MultiproofConeRef

def encodeIndices (indices : Fin 16 → Nat) : Array U32 16#usize :=
 ⟨List.ofFn (fun i => word (indices i)),by simp⟩
def decodeIndices (indices : Array U32 16#usize) (i : Fin 16) : Nat :=
 (indices.val[i.val]'(by have h := indices.property;change indices.val.length=16 at h;omega)).val

theorem indices_coordinate (indices : Fin 16 → Nat) (bounded : ∀ i, indices i < 2^32) (i : Fin 16) :
 decodeIndices (encodeIndices indices) i=indices i := by
 simp only [decodeIndices,encodeIndices,List.getElem_ofFn]
 exact word_value _ (bounded i)

theorem indices_roundtrip (indices : Array U32 16#usize) : encodeIndices (decodeIndices indices)=indices := by
 apply AspisR1.MultiproofConeNodeAdoption.array_ext
 intro j left right
 simp only [encodeIndices,List.getElem_ofFn,decodeIndices,word_roundtrip]

def raw (s : reference.Scratch) : Scratch where
 indices := decodeIndices s.idx
 values := decodeValues s.val
 n := s.n.val
 cursor := s.«at».val

def emitted (s : Scratch) : reference.Scratch where
 idx := encodeIndices s.indices
 val := encodeValues s.values
 n := size s.n
 «at» := size s.cursor

theorem roundtrip (s : reference.Scratch) : emitted (raw s)=s := by
 cases s
 simp only [emitted,raw,indices_roundtrip,values_roundtrip,size_roundtrip]

theorem faithful (left right : reference.Scratch) (same : raw left=raw right) : left=right := by
 rw [←roundtrip left,←roundtrip right,same]

theorem index_bound (s : reference.Scratch) (i : Fin 16) : (raw s).indices i < 2^32 := by
 change (s.idx.val[i.val]'_).val < 2^32
 exact (s.idx.val[i.val]'_).bv.isLt

#print indices_coordinate
#print axioms indices_coordinate
#print indices_roundtrip
#print axioms indices_roundtrip
#print roundtrip
#print axioms roundtrip
#print faithful
#print axioms faithful
#print index_bound
#print axioms index_bound
end NJP_ScratchCarrier
end
