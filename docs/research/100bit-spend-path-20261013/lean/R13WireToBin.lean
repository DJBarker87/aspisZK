import WireTx2BinaryCalls
import WireTx2LeafCalls
import BinGrammar

/-! Concrete byte-carrier transport from the retained stage-2 helpers to Bin.
The Digest32/oracle correspondence and the private-leaf backend law are
explicit hypotheses; no source array-loop correspondence is assumed here. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.R13WireToBin
open AspisR1Stage2 AspisR1Stage2.WireTx2
open BinMerkle32Path

def byte (b : U8) : BinMerkle32Path.Byte := b.bv.toFin

def bytes (bs : List U8) : List BinMerkle32Path.Byte := bs.map byte

def digest (a : Bytes32) : Digest := fun i =>
  byte (a.val[i.val]'(by have hlen : a.val.length = 32 := a.property; omega))

theorem digest_bytes (a : Bytes32) : List.ofFn (digest a) = bytes a.val := by
  apply List.ext_getElem
  · simp [bytes, a.property]
  · intro i hi hj
    simp only [bytes, List.getElem_ofFn, List.getElem_map, digest]

def children (left right : Bytes32) : Children :=
  fun i => if i = 0 then digest left else digest right

theorem node_bytes (left right : Bytes32) :
    bytes (inputBytes (nodeParts (Array.to_slice left) (Array.to_slice right))) =
      nodeInput (children left right) := by
  rw [BinGrammar.nodeInput_slices]
  simp only [children, if_true, if_false, show (1 : Fin 2) ≠ 0 by decide]
  rw [digest_bytes, digest_bytes]
  change bytes ([multiproof.BINARY_NODE_TAG] ++ (left.val ++ (right.val ++ []))) = _
  simp [bytes, byte, multiproof.BINARY_NODE_TAG]

theorem leaf_bytes (tag : U8) (packed : Slice U8) (salt : Bytes32) :
    bytes (inputBytes (leafParts tag packed salt)) =
      BinMerkle32Leaf.leafInput (byte tag) (bytes packed.val) (bytes salt.val) := by
  change bytes ([16#u8, tag] ++ (packed.val ++ (salt.val ++ []))) = _
  simp [bytes, byte, BinMerkle32Leaf.leafInput]

/-- The ordinary pure oracle interpretation of successful source digest calls.
This is the response correspondence boundary, not an instrumented global log. -/
def DigestLaw {T : Type} (D : aspis_core.digest.Digest32 T) (hash : T)
    (H : List BinMerkle32Path.Byte → Digest) : Prop :=
  ∀ parts out, D.digest hash parts = ok out →
    digest out = H (bytes (inputBytes parts))

theorem occupied_refines {T : Type} (D : aspis_core.digest.Digest32 T) (hash : T)
    (H : List BinMerkle32Path.Byte → Digest) (law : DigestLaw D hash H)
    (values : Array Bytes32 16#usize) (index : Usize) (out : Bytes32)
    (h : multiproof.occupied_binary_parent D hash values index = ok out) :
    ∃ left right : Bytes32, digest out = H (nodeInput (children left right)) := by
  obtain ⟨left, right, hd, _⟩ := occupied_typed D hash values index out h
  exact ⟨left, right, (law _ _ hd).trans (congrArg H (node_bytes left right))⟩

theorem leaf_refines (ops : LeafOps) (leafLaw : LeafDigestLaw ops)
    (c1 : ops.c1Tag = ok 113#u8) (c2 : ops.c2Tag = ok 241#u8)
    {T : Type} (D : aspis_core.digest.Digest32 T) (hash : T)
    (H : List BinMerkle32Path.Byte → Digest) (law : DigestLaw D hash H)
    (tree : Usize) (q : Slice U8) (out : Bytes32)
    (h : verifier.candidate.batch_leafWithWireOps ops D hash tree q = ok out) :
    ∃ (tag : U8) (packed : Slice U8) (salt : Bytes32),
      digest out = H (BinMerkle32Leaf.leafInput (byte tag)
        (bytes packed.val) (bytes salt.val)) ∧
      TypedInput (leafParts tag packed salt) := by
  obtain ⟨tag, packed, salt, hd, ht⟩ := batch_leaf_typed ops c1 c2 D hash tree q out h
  rw [leafLaw D hash tag packed salt] at hd
  exact ⟨tag, packed, salt, (law _ _ hd).trans (congrArg H (leaf_bytes tag packed salt)), ht⟩

#print axioms digest_bytes
#print axioms node_bytes
#print axioms leaf_bytes
#print axioms occupied_refines
#print axioms leaf_refines
end AspisR1.R13WireToBin
