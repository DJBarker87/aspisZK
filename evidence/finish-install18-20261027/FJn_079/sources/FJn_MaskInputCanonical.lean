import FIp_MaskNativeValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MaskInputCanonical
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic
/-- Canonicality transport of the SAME mapped array cell. -/
theorem cell {N : Usize} (a : Array MQ N)
    (all : ∀ x∈a.val,FIp_SemanticValues.Canon x) (i : Nat) (hi : i<a.val.length) :
    ExtractedMaskQM31Exact.CurrentCanonicalQM
      ((mapArray a).val[i]'(by simpa only [mapArray,List.length_map] using hi)) := by
  simp only [mapArray,List.getElem_map]
  exact all (a.val[i]'hi) (List.getElem_mem hi)
#print axioms cell
end AspisR1.FJn_MaskInputCanonical
end
