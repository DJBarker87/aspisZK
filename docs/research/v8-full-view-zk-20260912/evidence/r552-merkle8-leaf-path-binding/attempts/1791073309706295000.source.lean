import AspisV8PairedCommitment.Domains
import AspisV8R19.R549Merkle8PathBinding

/-! Generic literal tagged-leaf plus complete eight-way path binding.  No
parser, native execution, frontier, graph, probability, or security claim. -/
set_option autoImplicit false
namespace AspisV8R19.R552

open AspisV8PairedCommitment
open AspisV8R19.R549

abbrev Byte := Fin 256
abbrev Digest := Fin 26 → Byte

/-- Fixed-width packed payload and salt equality follows from the complete
literal leaf preimage; neither component is assumed equal in advance. -/
theorem leafInput_fixedWidth_injective (tag : Byte)
    (leftPacked leftSalt rightPacked rightSalt : List Byte)
    (leftWidth rightWidth : leftPacked.length = rightPacked.length)
    (hinput : leafInput tag leftPacked leftSalt = leafInput tag rightPacked rightSalt) :
    leftPacked = rightPacked ∧ leftSalt = rightSalt := by
  have htail := (List.cons.inj hinput).2
  have hpayload := (List.cons.inj htail).2
  exact List.append_inj hpayload leftWidth

/-- The selected C1 leaf tag and its 403-byte packed width. -/
def c1LeafInput (packed salt : List Byte) : List Byte := leafInput 0x71 packed salt

theorem c1_leafInput_length (packed salt : List Byte)
    (hp : packed.length = 403) (hs : salt.length = 32) :
    (c1LeafInput packed salt).length = 437 := by
  exact leaf_input_length 0x71 packed salt hs |>.trans (by omega)

/-- The selected C2 leaf tag and its 186-byte packed width. -/
def c2LeafInput (packed salt : List Byte) : List Byte := leafInput 0xf1 packed salt

theorem c2_leafInput_length (packed salt : List Byte)
    (hp : packed.length = 186) (hs : salt.length = 32) :
    (c2LeafInput packed salt).length = 220 := by
  exact leaf_input_length 0xf1 packed salt hs |>.trans (by omega)

theorem c1_c2_inputs_distinct (c1Packed c2Packed salt : List Byte) :
    c1LeafInput c1Packed salt ≠ c2LeafInput c2Packed salt := by
  exact literal_v7_pair_inputs_distinct c1Packed c2Packed salt

/-- The literal leaf input followed by every literal eight-way parent input. -/
def fullTrace (hash : List Byte → Digest) {slots : List (Fin 8)}
    (path : Path slots) (leaf : List Byte) : List (List Byte) :=
  leaf :: inputTrace hash path (hash leaf)

/-- A collision whose two preimages appear in the complete leaf-to-root traces. -/
def FullTraceCollision (hash : List Byte → Digest)
    (leftTrace rightTrace : List (List Byte)) : Prop :=
  CrossTraceCollision hash leftTrace rightTrace

/-- Same-tag fixed-width leaves at the same complete slot sequence either have
identical packed and salt records, or expose a distinct equal-hash pair from
the two full literal traces. -/
theorem leaf_path_binding {hash : List Byte → Digest}
    {slots : List (Fin 8)} (tag : Byte)
    (leftPath rightPath : Path slots)
    (leftPacked leftSalt rightPacked rightSalt : List Byte)
    (hpacked : leftPacked.length = rightPacked.length)
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
        rightPacked rightSalt hpacked hleaf)
    · exact Or.inr ⟨leftLeaf, by simp [fullTrace, leftLeaf],
        rightLeaf, by simp [fullTrace, rightLeaf], hleaf, hleafHash⟩
  · have hnode := foldPath_cross_trace_collision leftPath rightPath hleafHash sameRoot
    rcases hnode with ⟨a, ha, b, hb, hab, habHash⟩
    exact Or.inr ⟨a, by simp only [fullTrace, List.mem_cons]; exact Or.inr ha,
      b, by simp only [fullTrace, List.mem_cons]; exact Or.inr hb, hab, habHash⟩

/-- Exact selected C1 specialization: packed width 403 and salt width 32. -/
theorem c1_leaf_path_binding {hash : List Byte → Digest}
    {slots : List (Fin 8)} (leftPath rightPath : Path slots)
    (leftPacked leftSalt rightPacked rightSalt : List Byte)
    (hlp : leftPacked.length = 403) (hrp : rightPacked.length = 403)
    (hls : leftSalt.length = 32) (hrs : rightSalt.length = 32)
    (sameRoot : foldPath hash leftPath (hash (c1LeafInput leftPacked leftSalt)) =
      foldPath hash rightPath (hash (c1LeafInput rightPacked rightSalt))) :
    (leftPacked = rightPacked ∧ leftSalt = rightSalt) ∨ FullTraceCollision hash
      (fullTrace hash leftPath (c1LeafInput leftPacked leftSalt))
      (fullTrace hash rightPath (c1LeafInput rightPacked rightSalt)) := by
  exact leaf_path_binding 0x71 leftPath rightPath leftPacked leftSalt rightPacked rightSalt
    (hlp.trans hrp.symm) sameRoot

/-- Exact selected C2 specialization: packed width 186 and salt width 32. -/
theorem c2_leaf_path_binding {hash : List Byte → Digest}
    {slots : List (Fin 8)} (leftPath rightPath : Path slots)
    (leftPacked leftSalt rightPacked rightSalt : List Byte)
    (hlp : leftPacked.length = 186) (hrp : rightPacked.length = 186)
    (hls : leftSalt.length = 32) (hrs : rightSalt.length = 32)
    (sameRoot : foldPath hash leftPath (hash (c2LeafInput leftPacked leftSalt)) =
      foldPath hash rightPath (hash (c2LeafInput rightPacked rightSalt))) :
    (leftPacked = rightPacked ∧ leftSalt = rightSalt) ∨ FullTraceCollision hash
      (fullTrace hash leftPath (c2LeafInput leftPacked leftSalt))
      (fullTrace hash rightPath (c2LeafInput rightPacked rightSalt)) := by
  exact leaf_path_binding 0xf1 leftPath rightPath leftPacked leftSalt rightPacked rightSalt
    (hlp.trans hrp.symm) sameRoot

/-- Six-level selected-tree form; the full slot list remains explicit. -/
theorem depth6_leaf_path_binding {hash : List Byte → Digest}
    (slots : List (Fin 8)) (_hdepth : slots.length = 6) (tag : Byte)
    (leftPath rightPath : Path slots)
    (leftPacked leftSalt rightPacked rightSalt : List Byte)
    (hpacked : leftPacked.length = rightPacked.length)
    (sameRoot : foldPath hash leftPath (hash (leafInput tag leftPacked leftSalt)) =
      foldPath hash rightPath (hash (leafInput tag rightPacked rightSalt))) :
    (leftPacked = rightPacked ∧ leftSalt = rightSalt) ∨ FullTraceCollision hash
      (fullTrace hash leftPath (leafInput tag leftPacked leftSalt))
      (fullTrace hash rightPath (leafInput tag rightPacked rightSalt)) := by
  exact leaf_path_binding tag leftPath rightPath leftPacked leftSalt rightPacked rightSalt
    hpacked sameRoot

#print axioms leafInput_fixedWidth_injective
#print axioms c1_leafInput_length
#print axioms c2_leafInput_length
#print axioms c1_c2_inputs_distinct
#print axioms leaf_path_binding
#print axioms c1_leaf_path_binding
#print axioms c2_leaf_path_binding
#print axioms depth6_leaf_path_binding

end AspisV8R19.R552
