import BinMerkle32Path
import Mathlib.Data.List.Basic

/-! Mirrors `Merkle32Leaf.lean`; see design/BIN-COMMITMENT-MODEL-20261019.md for line pins.
 Literal tagged-leaf binding for the Merkle32 path model. This module
proves byte-list identities and a collision alternative only; it has no parser,
runtime, table-reconstruction, or probability statement. -/
set_option autoImplicit false
namespace AspisR1.BinMerkle32Leaf

open AspisR1.BinMerkle32Path

abbrev Byte := Fin 256

def leafInput (tag : Byte) (packed salt : List Byte) : List Byte :=
  0x10 :: tag :: (packed ++ salt)

theorem leaf_input_length (tag : Byte) (packed salt : List Byte)
    (hsalt : salt.length = 32) :
    (leafInput tag packed salt).length = packed.length + 34 := by
  simp [leafInput, hsalt]

theorem leafInput_fixedWidth_injective (tag : Byte)
    (leftPacked leftSalt rightPacked rightSalt : List Byte)
    (packedWidth : leftPacked.length = rightPacked.length)
    (hinput : leafInput tag leftPacked leftSalt =
      leafInput tag rightPacked rightSalt) :
    leftPacked = rightPacked ∧ leftSalt = rightSalt := by
  have htail := (List.cons.inj hinput).2
  have hpayload := (List.cons.inj htail).2
  exact List.append_inj hpayload packedWidth

def fullTrace (hash : List Byte → Digest) {slots : List (Fin 2)}
    (path : Path slots) (leaf : List Byte) : List (List Byte) :=
  leaf :: inputTrace hash path (hash leaf)

def FullTraceCollision (hash : List Byte → Digest)
    (leftTrace rightTrace : List (List Byte)) : Prop :=
  CrossTraceCollision hash leftTrace rightTrace

theorem leaf_path_binding {hash : List Byte → Digest}
    {slots : List (Fin 2)} (tag : Byte)
    (leftPath rightPath : Path slots)
    (leftPacked leftSalt rightPacked rightSalt : List Byte)
    (packedWidth : leftPacked.length = rightPacked.length)
    (sameRoot :
      foldPath hash leftPath (hash (leafInput tag leftPacked leftSalt)) =
      foldPath hash rightPath (hash (leafInput tag rightPacked rightSalt))) :
    (leftPacked = rightPacked ∧ leftSalt = rightSalt) ∨
      FullTraceCollision hash
        (fullTrace hash leftPath (leafInput tag leftPacked leftSalt))
        (fullTrace hash rightPath (leafInput tag rightPacked rightSalt)) := by
  let leftLeaf := leafInput tag leftPacked leftSalt
  let rightLeaf := leafInput tag rightPacked rightSalt
  by_cases hleafHash : hash leftLeaf = hash rightLeaf
  · by_cases hleaf : leftLeaf = rightLeaf
    · exact Or.inl (leafInput_fixedWidth_injective tag leftPacked leftSalt
        rightPacked rightSalt packedWidth hleaf)
    · exact Or.inr ⟨leftLeaf, by simp [fullTrace, leftLeaf],
        rightLeaf, by simp [fullTrace, rightLeaf], hleaf, hleafHash⟩
  · have hnode := foldPath_cross_trace_collision leftPath rightPath hleafHash sameRoot
    rcases hnode with ⟨a, ha, b, hb, hab, habHash⟩
    exact Or.inr ⟨a, by simp only [fullTrace, List.mem_cons]; exact Or.inr ha,
      b, by simp only [fullTrace, List.mem_cons]; exact Or.inr hb, hab, habHash⟩

def c1LeafInput (packed salt : List Byte) : List Byte :=
  leafInput 0x71 packed salt

def c2LeafInput (packed salt : List Byte) : List Byte :=
  leafInput 0xf1 packed salt

def foldedLeafInput (packed salt : List Byte) : List Byte :=
  leafInput 0x72 packed salt

theorem c1_leafInput_length (packed salt : List Byte)
    (packedWidth : packed.length = 480) (saltWidth : salt.length = 32) :
    (c1LeafInput packed salt).length = 514 := by
  simp [c1LeafInput, leafInput, packedWidth, saltWidth]

theorem c2_leafInput_length (packed salt : List Byte)
    (packedWidth : packed.length = 128) (saltWidth : salt.length = 32) :
    (c2LeafInput packed salt).length = 162 := by
  simp [c2LeafInput, leafInput, packedWidth, saltWidth]

theorem folded_leafInput_length (packed salt : List Byte)
    (packedWidth : packed.length = 128) (saltWidth : salt.length = 32) :
    (foldedLeafInput packed salt).length = 162 := by
  simp [foldedLeafInput, leafInput, packedWidth, saltWidth]

theorem c1_leaf_path_binding {hash : List Byte → Digest}
    {slots : List (Fin 2)} (leftPath rightPath : Path slots)
    (leftPacked leftSalt rightPacked rightSalt : List Byte)
    (leftPackedWidth : leftPacked.length = 480)
    (rightPackedWidth : rightPacked.length = 480)
    (leftSaltWidth : leftSalt.length = 32) (rightSaltWidth : rightSalt.length = 32)
    (sameRoot : foldPath hash leftPath (hash (c1LeafInput leftPacked leftSalt)) =
      foldPath hash rightPath (hash (c1LeafInput rightPacked rightSalt))) :
    (leftPacked = rightPacked ∧ leftSalt = rightSalt) ∨ FullTraceCollision hash
      (fullTrace hash leftPath (c1LeafInput leftPacked leftSalt))
      (fullTrace hash rightPath (c1LeafInput rightPacked rightSalt)) := by
  have _saltWidth : leftSalt.length = rightSalt.length := leftSaltWidth.trans rightSaltWidth.symm
  exact leaf_path_binding 0x71 leftPath rightPath leftPacked leftSalt rightPacked rightSalt
    (leftPackedWidth.trans rightPackedWidth.symm) sameRoot

theorem c2_leaf_path_binding {hash : List Byte → Digest}
    {slots : List (Fin 2)} (leftPath rightPath : Path slots)
    (leftPacked leftSalt rightPacked rightSalt : List Byte)
    (leftPackedWidth : leftPacked.length = 128)
    (rightPackedWidth : rightPacked.length = 128)
    (leftSaltWidth : leftSalt.length = 32) (rightSaltWidth : rightSalt.length = 32)
    (sameRoot : foldPath hash leftPath (hash (c2LeafInput leftPacked leftSalt)) =
      foldPath hash rightPath (hash (c2LeafInput rightPacked rightSalt))) :
    (leftPacked = rightPacked ∧ leftSalt = rightSalt) ∨ FullTraceCollision hash
      (fullTrace hash leftPath (c2LeafInput leftPacked leftSalt))
      (fullTrace hash rightPath (c2LeafInput rightPacked rightSalt)) := by
  have _saltWidth : leftSalt.length = rightSalt.length := leftSaltWidth.trans rightSaltWidth.symm
  exact leaf_path_binding 0xf1 leftPath rightPath leftPacked leftSalt rightPacked rightSalt
    (leftPackedWidth.trans rightPackedWidth.symm) sameRoot

theorem folded_leaf_path_binding {hash : List Byte → Digest}
    {slots : List (Fin 2)} (leftPath rightPath : Path slots)
    (leftPacked leftSalt rightPacked rightSalt : List Byte)
    (leftPackedWidth : leftPacked.length = 128)
    (rightPackedWidth : rightPacked.length = 128)
    (leftSaltWidth : leftSalt.length = 32) (rightSaltWidth : rightSalt.length = 32)
    (sameRoot : foldPath hash leftPath (hash (foldedLeafInput leftPacked leftSalt)) =
      foldPath hash rightPath (hash (foldedLeafInput rightPacked rightSalt))) :
    (leftPacked = rightPacked ∧ leftSalt = rightSalt) ∨ FullTraceCollision hash
      (fullTrace hash leftPath (foldedLeafInput leftPacked leftSalt))
      (fullTrace hash rightPath (foldedLeafInput rightPacked rightSalt)) := by
  have _saltWidth : leftSalt.length = rightSalt.length := leftSaltWidth.trans rightSaltWidth.symm
  exact leaf_path_binding 0x72 leftPath rightPath leftPacked leftSalt rightPacked rightSalt
    (leftPackedWidth.trans rightPackedWidth.symm) sameRoot


#print axioms leaf_input_length
#print axioms leafInput_fixedWidth_injective
#print axioms leaf_path_binding
#print axioms c1_leafInput_length
#print axioms c2_leafInput_length
#print axioms folded_leafInput_length
#print axioms c1_leaf_path_binding
#print axioms c2_leaf_path_binding
#print axioms folded_leaf_path_binding

end AspisR1.BinMerkle32Leaf
