import AspisV8PairedCommitment.Domains

/-!
# Pinned V8/V7-compact leaf grammar

This is the literal byte boundary used by the selected source path at
`b0c738e`: the prover packs 104 M31 limbs into 403 bytes for C1 and 48 M31
limbs into 186 bytes for C2; the verifier hashes those packed bytes with the
same disclosed 32-byte salt. Canonical-field validation is a separate parser
check and is not inferred from these length lemmas.

The production names retain `V7` because V8 privacy work targets the existing
compact wire. No production definition is changed here.
-/
set_option autoImplicit false
namespace AspisV8PairedCommitment

def v8C1LeafInput (packed salt : List Byte) : List Byte :=
  leafInput 113 packed salt

def v8C2LeafInput (packed salt : List Byte) : List Byte :=
  leafInput 241 packed salt

theorem v8_c1_leaf_input_length (packed salt : List Byte)
    (packedWidth : packed.length = 403) (saltWidth : salt.length = 32) :
    (v8C1LeafInput packed salt).length = 437 := by
  simp [v8C1LeafInput, leafInput, packedWidth, saltWidth]

theorem v8_c2_leaf_input_length (packed salt : List Byte)
    (packedWidth : packed.length = 186) (saltWidth : salt.length = 32) :
    (v8C2LeafInput packed salt).length = 220 := by
  simp [v8C2LeafInput, leafInput, packedWidth, saltWidth]

theorem v8_paired_leaf_inputs_distinct
    (c1Packed c2Packed salt : List Byte) :
    v8C1LeafInput c1Packed salt ≠ v8C2LeafInput c2Packed salt := by
  exact literal_v7_pair_inputs_distinct c1Packed c2Packed salt

theorem v8_parent_ne_c1_leaf
    (left right packed salt : List Byte) :
    parentInput left right ≠ v8C1LeafInput packed salt := by
  exact parent_input_ne_leaf_input left right packed salt 113

theorem v8_parent_ne_c2_leaf
    (left right packed salt : List Byte) :
    parentInput left right ≠ v8C2LeafInput packed salt := by
  exact parent_input_ne_leaf_input left right packed salt 241

#print axioms v8_c1_leaf_input_length
#print axioms v8_c2_leaf_input_length
#print axioms v8_paired_leaf_inputs_distinct
#print axioms v8_parent_ne_c1_leaf
#print axioms v8_parent_ne_c2_leaf
end AspisV8PairedCommitment
