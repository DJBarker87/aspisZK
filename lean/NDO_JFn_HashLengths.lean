import NDO_JFn_HashBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_HashLengths
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem proof : (flatten JFn_HashBoundary.proofParts).length=57607 := by
  simp only [JFn_HashBoundary.proofParts,flatten,Array.to_slice,Array.make,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_map]
  exact JFx_NativeBytes.proofBytes_length

theorem publicInput : (flatten JFn_HashBoundary.publicParts).length=1880 := by
  simp only [JFn_HashBoundary.publicParts,flatten,Array.to_slice,Array.make,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_map]
  exact JFx_NativeBytes.publicBytes_length

theorem checksum : (flatten JFn_HashBoundary.checksumParts).length=1758 := by
  simp only [JFn_HashBoundary.checksumParts,flatten,Array.to_slice,Array.make,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_map,List.length_append,
    JFq_Range.length,List.length_cons,List.length_nil]

/-- The three actual oracle inputs are different by size. This proves
consistency of their finite assignments, not any numeric SHA256 equation. -/
theorem distinct : flatten JFn_HashBoundary.proofParts≠flatten JFn_HashBoundary.publicParts ∧
    flatten JFn_HashBoundary.proofParts≠flatten JFn_HashBoundary.checksumParts ∧
    flatten JFn_HashBoundary.publicParts≠flatten JFn_HashBoundary.checksumParts := by
  refine ⟨?_,?_,?_⟩
  all_goals intro h;have size:=congrArg List.length h
  · rw [proof,publicInput] at size;omega
  · rw [proof,checksum] at size;omega
  · rw [publicInput,checksum] at size;omega

#print axioms proof
#print axioms publicInput
#print axioms checksum
#print axioms distinct
end AspisR1.JFn_HashLengths
end
