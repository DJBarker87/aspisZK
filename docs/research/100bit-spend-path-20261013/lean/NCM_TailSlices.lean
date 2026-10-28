import NCM_PaddingRun

set_option autoImplicit false
namespace AspisR1.NCM_TailSlices
open Aeneas Aeneas.Std

def suffix (nodes : Slice U8) (count : Nat) : Slice U8 :=
  ⟨nodes.val.drop (32*count),by have := nodes.property;simp only [List.length_drop];omega⟩

/-- Same physical suffix length establishes whole 8-byte words. -/
theorem suffix_length (nodes : Slice U8) (count cap : Nat) (fit : count ≤ cap)
    (size : nodes.val.length = 32*cap) :
    (suffix nodes count).val.length = 8*(4*(cap-count)) := by
  simp only [suffix,List.length_drop,size]
  omega

/-- No new bytes, permutation or independent buffer enters padding. -/
theorem suffix_bytes (nodes : Slice U8) (count : Nat) :
    MultiproofConeCanonical.bytesOf (suffix nodes count).val =
      (MultiproofConeCanonical.bytesOf nodes.val).drop (32*count) := by
  simp only [suffix,MultiproofConeCanonical.bytesOf,List.map_drop]

/-- The same exact count selects the verifier prefix. -/
theorem prefix_length (nodes : Slice U8) (count cap : Nat) (fit : count ≤ cap)
    (size : nodes.val.length = 32*cap) :
    (MultiproofConeSlotTail.prefixNodes nodes count).val.length = 32*count := by
  simp only [MultiproofConeSlotTail.prefixNodes,List.length_take,size]
  omega

#print axioms suffix_length
#print axioms suffix_bytes
#print axioms prefix_length
end AspisR1.NCM_TailSlices
