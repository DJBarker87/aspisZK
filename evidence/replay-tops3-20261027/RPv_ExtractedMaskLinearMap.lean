import ExtractedMaskLinearRecurrence

/-! A ring hom transports the local mask-linear formula term by term.
This is the carrier bridge needed before comparing the extracted QM31Exact
computation with the WideExact semantic formula. It does not identify the two
carriers and makes no source-refinement claim. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskLinearMap

open AspisR1.ExtractedMaskLinearRecurrence

theorem map_maskLinear {K L : Type} [Field K] [Field L]
    (f : K →+* L) (family : Nat) (α : Fin 10 → K) :
    f (maskLinear family α) = maskLinear family (fun i => f (α i)) := by
  unfold maskLinear
  simp only [map_sum, map_mul, map_natCast]

#print axioms map_maskLinear

end AspisR1.ExtractedMaskLinearMap
