import NDH_HashBridge
set_option autoImplicit false
namespace NJS_DigestLeaves
open Aeneas Aeneas.Std Result
/-- Reuse the extracted safe-reference grammar. Its native association is NJS_K008/009;
all input lengths, including the deployed480-byte branch, are covered by the grammar.
The runtime's digest VALUE remains the existing SHA realization hypothesis. -/
theorem leaf {H : Type} (D : NDH_TranscriptReference.NDH_DigestRef H) (hash : H)
    (oracle : List (Fin 256) → Result (Array U8 32#usize))
    (runtime : ∀ parts, D.digest hash parts = oracle (NDH_HashBridge.input parts))
    (tag : U8) (value : Slice U8) (salt : Array U8 32#usize) :
    NDH_TranscriptReference.leaf_ref D hash tag value salt =
      oracle (AspisR1.Merkle32Leaf.leafInput (NDH_MerkleGrammar.byte tag)
        (value.val.map NDH_MerkleGrammar.byte) (salt.val.map NDH_MerkleGrammar.byte)) :=
  NDH_HashBridge.leaf D hash oracle runtime tag value salt

theorem parent {H : Type} (D : NDH_TranscriptReference.NDH_DigestRef H) (hash : H)
    (oracle : List (Fin 256) → Result (Array U8 32#usize))
    (runtime : ∀ parts, D.digest hash parts = oracle (NDH_HashBridge.input parts))
    (children : Array (Array U8 32#usize) 8#usize) :
    NDH_TranscriptReference.parent_ref D hash children =
      oracle (AspisR1.Merkle32Path.nodeInput (NDH_MerkleGrammar.children children)) :=
  NDH_HashBridge.parent D hash oracle runtime children

#check leaf
#check parent
#print axioms leaf
#print axioms parent
end NJS_DigestLeaves
