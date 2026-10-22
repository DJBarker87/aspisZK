import S9TwoCallScalarMeaningV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ConcreteScalarCallSemanticsV1

local instance selectedOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev W := Array AspisR1S9HelperP6.field.WideExact (4#usize)
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev U := Std.Usize
abbrev CurrentQM := AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
abbrev ScalarMeaning := AspisR1S9TwoCallScalarMeaningV2.ScalarMeaning

/-- Canonicality of the very output returned by one concrete selected
`scalar_factor` call. The canonical pre-quarter accumulator is recovered from
the four successful callback steps of that same call, then the exact final
quarter multiplication is used to establish canonicality of `low`. -/
theorem concrete_scalar_factor_low_canonical
    (ap0 : W) (q1 : Array Q (4#usize)) (low : S) (seed : Q)
    (hp : ∀ (j : U) (x : S), Array.index_usize ap0 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hseed : AspisR1CurrentWide.Proof.CanonicalQM (CurrentQM seed))
    (hkp : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize) seed = .ok q1)
    (hscalar : @AspisR1S9HelperP6.weights.Weights.scalar_factor
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q1 ap0 = .ok low) :
    AspisR1S9CurrentFieldOpsV1.Canonical low := by
  have hcurrentPowers : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps (4#usize) seed = .ok q1 := by
    simpa only [AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps] using
      (AspisR1S9ConcreteFieldOpsV1.kpowers_concrete_eq_current (4#usize) seed).symm.trans hkp
  have hqvalues : ∀ (index : U) (x : Q), Array.index_usize q1 index = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM x) := by
    intro index x hread
    have hcan := AspisR1S9ScalarFactorKpowersReadV1.kpowers_success_read_current
      seed q1 hseed hcurrentPowers index x hread
    simpa only [AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics,
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM,
      AspisR1S9GeneratedWideMulQM31V2.toQM] using hcan.1
  have hfold : AspisR1S9HelperP6.IteratorFoldRangeP6Law
      (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps
        (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
          AspisR1S9ConcreteFieldOpsV1.concreteFieldOps)) :=
    AspisR1S9TransparentFoldActualOpsConsumerV1.actualFactorOps_after_extractedFold_satisfies_P6
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
  have hscalarInstalled : (letI : AspisR1S9HelperP6.FieldOps :=
      (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps
        (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
          AspisR1S9ConcreteFieldOpsV1.concreteFieldOps))
      AspisR1S9HelperP6.weights.Weights.scalar_factor q1 ap0) = .ok low := by
    rw [AspisR1S9TwoCallScalarMeaningV2.concrete_factor_ops_eq]
    exact hscalar
  letI : AspisR1S9HelperP6.FieldOps :=
    (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps
      (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps))
  obtain ⟨we, s0, s1, s2, hmul, h0, h1, h2, h3⟩ :=
    AspisR1S9ScalarFactorFourFoldV1.scalar_factor_success_four_fold_calls
      (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps)
      q1 ap0 low hfold hscalarInstalled
  have h0m := AspisR1S9ScalarFactorFourFoldMeaningV1.scalarStep_actual_meaning
    (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps)
    ap0 q1 AspisR1S9HelperP6.field.WideExact.ZERO s0.1 0#usize s0.2
    (by simpa using h0)
    AspisR1S9TransparentFoldS2InstanceV1.zero_canonical hp hqvalues
  rcases h0m with ⟨hs0c, _j0, _p0, _q0, _hperm0, _hp0, _hq0, hc0, _hd0⟩
  have h1' := h1
  change AspisR1S9ScalarFactorFourFoldV1.scalarStep
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      (s0.1, s0.2) 1#usize = .ok s1 at h1'
  rw [hs0c] at h1'
  have h1m := AspisR1S9ScalarFactorFourFoldMeaningV1.scalarStep_actual_meaning
    (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps)
    ap0 q1 s0.1 s1.1 1#usize s1.2 (by simpa using h1') hc0 hp hqvalues
  rcases h1m with ⟨hs1c, _j1, _p1, _q1, _hperm1, _hp1, _hq1, hc1, _hd1⟩
  have h2' := h2
  change AspisR1S9ScalarFactorFourFoldV1.scalarStep
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      (s1.1, s1.2) 2#usize = .ok s2 at h2'
  rw [hs1c] at h2'
  have h2m := AspisR1S9ScalarFactorFourFoldMeaningV1.scalarStep_actual_meaning
    (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps)
    ap0 q1 s1.1 s2.1 2#usize s2.2 (by simpa using h2') hc1 hp hqvalues
  rcases h2m with ⟨hs2c, _j2, _p2, _q2, _hperm2, _hp2, _hq2, hc2, _hd2⟩
  have h3' := h3
  change AspisR1S9ScalarFactorFourFoldV1.scalarStep
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      (s2.1, s2.2) 3#usize = .ok (we, (ap0, q1)) at h3'
  rw [hs2c] at h3'
  have h3m := AspisR1S9ScalarFactorFourFoldMeaningV1.scalarStep_actual_meaning
    (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps)
    ap0 q1 s2.1 we 3#usize (ap0, q1) (by simpa using h3') hc2 hp hqvalues
  rcases h3m with ⟨_hc3, ⟨_, _, _, _, _, _, hwecan, _⟩⟩
  exact (AspisR1S9CurrentFieldOpsV1.actualWideMulM31_success
    we low AspisR1S9HelperP6.weights.QUARTER hwecan hmul).1

/-- The concrete source scalar call also has the established S2 polynomial
meaning over its exact returned `kpowers` and low arrays. -/
theorem concrete_scalar_factor_s2_meaning
    (ap0 : W) (q1 : Array Q (4#usize)) (low : S) (seed : Q)
    (hseed : AspisR1CurrentWide.Proof.CanonicalQM (CurrentQM seed))
    (hkp : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize) seed = .ok q1)
    (hscalar : @AspisR1S9HelperP6.weights.Weights.scalar_factor
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q1 ap0 = .ok low)
    (hp : ∀ (j : U) (x : S), Array.index_usize ap0 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x) :
    ScalarMeaning ap0 q1 low seed := by
  have hinstalled : (letI : AspisR1S9HelperP6.FieldOps :=
      (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps
        (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
          AspisR1S9ConcreteFieldOpsV1.concreteFieldOps))
      AspisR1S9HelperP6.weights.Weights.scalar_factor q1 ap0) = .ok low := by
    rw [AspisR1S9TwoCallScalarMeaningV2.concrete_factor_ops_eq]
    exact hscalar
  have hpowers : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps (4#usize) seed = .ok q1 := by
    simpa only [AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps] using
      (AspisR1S9ConcreteFieldOpsV1.kpowers_concrete_eq_current (4#usize) seed).symm.trans hkp
  exact AspisR1S9TransparentFoldS2InstanceV1.scalar_factor_success_is_s2_scalar
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 q1 low seed
    hinstalled hp hseed hpowers

#print axioms concrete_scalar_factor_low_canonical
#print axioms concrete_scalar_factor_s2_meaning

end AspisR1S9ConcreteScalarCallSemanticsV1
