import NDH_TranscriptReference.Funs
import NDH_MerkleGrammar
set_option autoImplicit false
namespace NDH_HashBridge
open Aeneas Aeneas.Std Result
open AspisR1 NDH_MerkleGrammar

def input (parts : Slice (Slice U8)) : List (Fin 256) :=
  parts.val.flatMap (fun part => part.val.map byte)

/-- The handler interpretation is the retained runtime sha256=H realization.
It is not a new hash-value proof or a supplied caller-output equality. -/
theorem leaf {H : Type} (D : NDH_TranscriptReference.NDH_DigestRef H) (hash : H)
    (oracle : List (Fin 256) → Result (Array U8 32#usize))
    (physical : ∀ parts, D.digest hash parts = oracle (input parts))
    (tag : U8) (value : Slice U8) (salt : Array U8 32#usize) :
    NDH_TranscriptReference.leaf_ref D hash tag value salt =
      oracle (Merkle32Leaf.leafInput (byte tag) (value.val.map byte) (salt.val.map byte)) := by
  simp only [NDH_TranscriptReference.leaf_ref,lift,bind_tc_ok,physical]
  change oracle (([byte 16#u8,byte tag] ++ (value.val.map byte ++ (salt.val.map byte ++ [])))) = _
  simp only [List.append_nil,Merkle32Leaf.leafInput]
  rfl

theorem parent {H : Type} (D : NDH_TranscriptReference.NDH_DigestRef H) (hash : H)
    (oracle : List (Fin 256) → Result (Array U8 32#usize))
    (physical : ∀ parts, D.digest hash parts = oracle (input parts))
    (c : Array (Array U8 32#usize) 8#usize) :
    NDH_TranscriptReference.parent_ref D hash c =
      oracle (Merkle32Path.nodeInput (children c)) := by
  have i0 : Array.index_usize c 0#usize = ok (row c 0) := by
    simpa [row] using NDH_ArrayIndex.array_index_usize_ok c 0#usize (by decide)
  have i1 : Array.index_usize c 1#usize = ok (row c 1) := by
    simpa [row] using NDH_ArrayIndex.array_index_usize_ok c 1#usize (by decide)
  have i2 : Array.index_usize c 2#usize = ok (row c 2) := by
    simpa [row] using NDH_ArrayIndex.array_index_usize_ok c 2#usize (by decide)
  have i3 : Array.index_usize c 3#usize = ok (row c 3) := by
    simpa [row] using NDH_ArrayIndex.array_index_usize_ok c 3#usize (by decide)
  have i4 : Array.index_usize c 4#usize = ok (row c 4) := by
    simpa [row] using NDH_ArrayIndex.array_index_usize_ok c 4#usize (by decide)
  have i5 : Array.index_usize c 5#usize = ok (row c 5) := by
    simpa [row] using NDH_ArrayIndex.array_index_usize_ok c 5#usize (by decide)
  have i6 : Array.index_usize c 6#usize = ok (row c 6) := by
    simpa [row] using NDH_ArrayIndex.array_index_usize_ok c 6#usize (by decide)
  have i7 : Array.index_usize c 7#usize = ok (row c 7) := by
    simpa [row] using NDH_ArrayIndex.array_index_usize_ok c 7#usize (by decide)
  simp only [NDH_TranscriptReference.parent_ref,i0,i1,i2,i3,i4,i5,i6,i7,lift,bind_tc_ok,physical]
  rw [←NDH_MerkleGrammar.node c]
  congr 1
  simp only [input,sourceNode,List.ofFn_succ,List.ofFn_zero,
    List.flatten_cons,List.flatten_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  try rfl

#print axioms leaf
#print axioms parent
end NDH_HashBridge
