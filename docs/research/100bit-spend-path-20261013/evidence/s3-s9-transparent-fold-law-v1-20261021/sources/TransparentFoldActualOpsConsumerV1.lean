import TransparentFoldRangeLawV1
import S3S9ScalarFactorActualOpsStepV1
import S3S9ScalarFactorPowerPolynomialV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9TransparentFoldActualOpsConsumerV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31

/-- The actual scalar-factor field operations update add/multiply slots only;
they retain the exact extracted Std fold installed in the input record. -/
theorem actualFactorOps_after_extractedFold_satisfies_P6 (ops : Ops) :
    AspisR1S9HelperP6.IteratorFoldRangeP6Law
      (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps
        (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)) := by
  intro B F callback range initial closure
  change AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      callback range initial closure =
    AspisR1S9HelperP6.iterFoldRange callback range initial closure
  exact AspisR1S9TransparentFoldRangeLawV1.extracted_fold_eq_rangeFoldRun
    callback range initial closure

/-- The existing four-term polynomial theorem can now be applied to the
actual scalar-factor operations with the extracted transparent fold installed;
the Std-fold premise is derived here rather than supplied independently. -/
theorem scalar_factor_four_term_polynomial_from_extracted_fold
    (ops : Ops) (p : Array S 4#usize) (f : Array Q 4#usize)
    (out : S) (seed : Q)
    (hscalar : (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)
      AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out)
    (hzeroCan : AspisR1S9ScalarFactorFourFoldMeaningV1.CanonicalS
      AspisR1S9HelperP6.field.WideExact.ZERO)
    (hzeroDecode : AspisR1S9ScalarFactorFourFoldMeaningV1.DecodeS
      AspisR1S9HelperP6.field.WideExact.ZERO = 0)
    (hpvalues : ∀ (index : Std.Usize) (x : S),
      Array.index_usize p index = .ok x →
        AspisR1S9ScalarFactorFourFoldMeaningV1.CanonicalS x)
    (hseed : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed))
    (hpowers : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
      (4#usize) seed = .ok f) :
    ∃ (we : S) (j0 j1 j2 j3 : Std.Usize)
      (p0 p1 p2 p3 : S) (q0 q1 q2 q3 : Q),
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1S9CurrentFieldOpsV1.toE we) ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 0#usize = .ok j0 ∧
      Array.index_usize p j0 = .ok p0 ∧ Array.index_usize f 0#usize = .ok q0 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 1#usize = .ok j1 ∧
      Array.index_usize p j1 = .ok p1 ∧ Array.index_usize f 1#usize = .ok q1 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 2#usize = .ok j2 ∧
      Array.index_usize p j2 = .ok p2 ∧ Array.index_usize f 2#usize = .ok q2 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 3#usize = .ok j3 ∧
      Array.index_usize p j3 = .ok p3 ∧ Array.index_usize f 3#usize = .ok q3 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9CurrentFieldOpsV1.toE out) =
        (((AspisR1CurrentWide.Proof.decodeWide
              (AspisR1S9CurrentFieldOpsV1.toE p0) +
            AspisR1S9ScalarFactorPowerPolynomialV1.powerTerm p1
              (AspisR1CurrentWide.Proof.decodeQM
                (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)) 1) +
          AspisR1S9ScalarFactorPowerPolynomialV1.powerTerm p2
            (AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)) 2) +
        AspisR1S9ScalarFactorPowerPolynomialV1.powerTerm p3
          (AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)) 3) *
          AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER ∧
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q0) =
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 0 ∧
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q1) =
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 1 ∧
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q2) =
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 2 ∧
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q3) =
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed) ^ 3 := by
  exact AspisR1S9ScalarFactorPowerPolynomialV1.scalar_factor_kpowers_four_term_polynomial
    (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold ops)
    p f out seed
    (actualFactorOps_after_extractedFold_satisfies_P6 ops)
    hscalar hzeroCan hzeroDecode hpvalues hseed hpowers

#print axioms actualFactorOps_after_extractedFold_satisfies_P6
#print axioms scalar_factor_four_term_polynomial_from_extracted_fold

end AspisR1S9TransparentFoldActualOpsConsumerV1
