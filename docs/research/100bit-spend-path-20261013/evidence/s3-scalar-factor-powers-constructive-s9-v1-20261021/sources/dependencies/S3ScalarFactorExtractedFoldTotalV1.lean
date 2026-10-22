import S3ScalarFactorTotalV1
import TransparentFoldActualOpsConsumerV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S3ScalarFactorExtractedFoldTotalV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev U := Std.Usize

/-- Constructive success for the scalar-factor model using the exact
transparent extracted iterator fold installed before the actual arithmetic
ops. The fold-law premise and any successful-execution premise are derived,
not supplied. The remaining assumptions are canonical values on successful
in-range reads from the two caller-provided arrays. -/
theorem scalar_factor_total_with_extracted_fold
    (ops : Ops) (p : Array S (4#usize)) (f : Array Q (4#usize))
    (hp : ∀ (j : U) (x : S), Array.index_usize p j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hf : ∀ (j : U) (x : Q), Array.index_usize f j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM x)) :
    ∃ out,
      (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps
        (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)
       AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out := by
  exact AspisR1S3ScalarFactorTotalV1.scalar_factor_total_of_canonical_arrays
    (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)
    p f
    (AspisR1S9TransparentFoldActualOpsConsumerV1.actualFactorOps_after_extractedFold_satisfies_P6 ops)
    hp hf

#print axioms scalar_factor_total_with_extracted_fold

end AspisR1S3ScalarFactorExtractedFoldTotalV1
