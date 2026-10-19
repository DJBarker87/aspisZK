import RawPrivateLeafCall
import RawMerkleAcceptedTrace

/-! A successful actual private leaf call plus emitted candidate path check
supplies the ideal salted-leaf authentication statement and its full trace.
Complete caller/log inclusion remains explicit. -/
set_option autoImplicit false
namespace AspisR1PrivateLeaf.RawPrivateLeafAcceptedPath
open Aeneas Aeneas.Std Result
open RawPrivateLeafCall
open AspisR1MerklePathChildren.RawMerkleParentBytes (decodeByte decodeDigest flattenParts)
open AspisR1MerklePathChildren.RawMerkleAcceptedLiteralPath (ParentCall positions)
open AspisR1MerklePathChildren.RawMerkleAcceptedTrace (rawLog accepted_global_trace)
open AspisR1.Merkle32Path (Path foldPath inputTrace)
open AspisR1.Merkle32Leaf (leafInput fullTrace)

def fullRawLog {H : Type} {D : AspisR1MerklePathChildren.Digest32 H} {hash : H}
    (tag : U8) (value : Slice U8) (salt node : Digest)
    (calls : List (ParentCall D hash)) :=
  (flattenParts (leafParts tag value salt),decodeDigest node) :: rawLog calls

theorem accepted_private_leaf_path {H : Type}
    (DL : Digest32 H) (DM : AspisR1MerklePathChildren.Digest32 H) (hash : H)
    (tag : U8) (value : Slice U8) (salt node root : Digest)
    (index : Usize) (path : Slice U8)
    (hleaf : state_only_private_merkle.private_leaf_hash_with_digest DL hash tag value salt = ok node)
    (hpath : AspisR1MerklePathChildren.verifier.merkle_path DM hash root index node path = ok true) :
    ∃ (calls : List (ParentCall DM hash)) (slots : List (Fin 8)) (p : Path slots),
      calls.length = 6 ∧ slots.map Fin.val = positions index.val 6 ∧
      ∀ (oracle : List (Fin 256) → AspisR1.Merkle32Path.Digest)
        (tr : List (List (Fin 256) × AspisR1.Merkle32Path.Digest)),
        (∀ q ∈ fullRawLog tag value salt node calls, q ∈ tr) →
        (∀ q ∈ tr, q.2 = oracle q.1) →
        foldPath oracle p (oracle (leafInput (decodeByte tag)
          (value.val.map decodeByte) (salt.val.map decodeByte))) = decodeDigest root ∧
        fullRawLog tag value salt node calls =
          (fullTrace oracle p (leafInput (decodeByte tag)
            (value.val.map decodeByte) (salt.val.map decodeByte))).map
            (fun input => (input,oracle input)) := by
  obtain ⟨calls,slots,p,hcount,hpositions,haccepted⟩ :=
    accepted_global_trace DM hash root index node path hpath
  refine ⟨calls,slots,p,hcount,hpositions,?_⟩
  intro oracle tr hsub hglobal
  have hleafread : (flattenParts (leafParts tag value salt),decodeDigest node) ∈ tr :=
    hsub _ (List.mem_cons_self ..)
  have hparents : ∀ q ∈ rawLog calls, q ∈ tr := by
    intro q hq
    exact hsub q (List.mem_cons_of_mem _ hq)
  have hnode := (successful_leaf_global DL hash tag value salt node hleaf
    oracle tr hleafread hglobal).2
  obtain ⟨hroot,htrace⟩ := haccepted oracle tr hparents hglobal
  refine ⟨?_,?_⟩
  · rwa [← hnode]
  · simp only [fullRawLog,fullTrace,List.map_cons,← hnode]
    rw [leaf_literal_bytes,htrace]

#print axioms accepted_private_leaf_path
end AspisR1PrivateLeaf.RawPrivateLeafAcceptedPath
