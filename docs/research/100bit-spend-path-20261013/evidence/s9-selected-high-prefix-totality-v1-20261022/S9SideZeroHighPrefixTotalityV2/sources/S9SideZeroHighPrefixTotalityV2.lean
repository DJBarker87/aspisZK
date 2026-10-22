import KpowersCurrentQMSemanticsV1
import S3KpowersTotalConstructiveV1
import S3S9ScalarFactorKpowersReadV1
import S3ScalarFactorExtractedFoldTotalV1
import S9ConcreteScalarCallSemanticsV1
import S3S9ConcreteSquareSemanticsV1
import S9QMMulTotalCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9SideZeroHighPrefixTotalityV2

open AspisR1S9HelperP6
open AspisR1S9HelperP6PowerSemanticsV1

local instance selectedOps : FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev U := Std.Usize
abbrev Q := field.QM31
abbrev W := field.WideExact
abbrev FourW := Array W (4#usize)
abbrev TwoQ := Array Q (2#usize)

/-- From canonical source reads, the actual selected side-zero scalar prefix
constructs its seed read, generated four-entry `kpowers` result, and actual
`scalar_factor` result. The returned low value is canonical, so the following
three term additions and side-zero tail can consume it. No child success is
assumed. -/
theorem side_zero_scalar_prefix_total
    (ap0 : FourW) (extra : TwoQ)
    (hap0 : ∀ (j : U) (x : W), Array.index_usize ap0 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hextra : ∀ (j : U) (q : Q), Array.index_usize extra j = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q)) :
    ∃ (seed : Q) (q1 : Array Q (4#usize)) (low : W),
      Array.index_usize extra 0#usize = .ok seed ∧
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) seed = .ok q1 ∧
      @weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        q1 ap0 = .ok low ∧
      AspisR1S9CurrentFieldOpsV1.Canonical low := by
  have htwo : (2#usize).val = 2 := by decide
  obtain ⟨seed, hseed, _⟩ := WP.spec_imp_exists
    (Array.index_usize_spec extra 0#usize
      (by simpa [extra.property, htwo] using (show (0#usize).val < 2 from by decide)))
  have hseedCan : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM seed) := hextra 0#usize seed hseed
  obtain ⟨q1, hq1Current⟩ :=
    AspisR1S3KpowersTotalConstructiveV1.kpowers_success_of_canonical_seed
      seed hseedCan
  have hq1Concrete : @weights.kpowers
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize) seed = .ok q1 := by
    simpa only [currentFieldOps] using
      (AspisR1S9ConcreteFieldOpsV1.kpowers_concrete_eq_current
        (4#usize) seed).trans hq1Current
  have hq1CurrentField : @weights.kpowers currentQMOps
      (4#usize) seed = .ok q1 := by
    simpa only [currentFieldOps] using hq1Current
  have hq1Values : ∀ (j : U) (x : Q), Array.index_usize q1 j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM x) := by
    intro j x hread
    have hcan := AspisR1S9ScalarFactorKpowersReadV1.kpowers_success_read_current
      seed q1 hseedCan hq1CurrentField j x hread
    simpa only [currentQMSemantics, helperToCurrentQM,
      AspisR1S9GeneratedWideMulQM31V2.toQM] using hcan.1
  obtain ⟨low, hscalarInstalled⟩ :=
    AspisR1S3ScalarFactorExtractedFoldTotalV1.scalar_factor_total_with_extracted_fold
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 q1 hap0 hq1Values
  have hscalar : @weights.Weights.scalar_factor
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q1 ap0 = .ok low := by
    rw [AspisR1S9TwoCallScalarMeaningV2.concrete_factor_ops_eq] at hscalarInstalled
    exact hscalarInstalled
  have hlowCan := AspisR1S9ConcreteScalarCallSemanticsV1.concrete_scalar_factor_low_canonical
    ap0 q1 low seed hap0 hseedCan hq1Concrete hscalar
  exact ⟨seed, q1, low, hseed, hq1Concrete, hscalar, hlowCan⟩


/-- Extend the same actual selected side-zero prefix through the exact q2,
q4, q8, q12 and q16 operations that precede scalar_factor/from_fn in
`activeBody`. All operation results are constructed from canonicality, not
assumed as successful premises. -/
theorem side_zero_high_prefix_total
    (ap0 : FourW) (extra : TwoQ)
    (hap0 : ∀ (j : U) (x : W), Array.index_usize ap0 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hextra : ∀ (j : U) (q : Q), Array.index_usize extra j = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q)) :
    ∃ (seed : Q) (q1 : Array Q (4#usize)) (q2 q4 q8 q12 q16 : Q) (low : W),
      Array.index_usize extra 0#usize = .ok seed ∧
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) seed = .ok q1 ∧
      Array.index_usize q1 2#usize = .ok q2 ∧
      @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q2 = .ok q4 ∧
      @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q4 = .ok q8 ∧
      @FieldOps.qmMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q8 q4 = .ok q12 ∧
      @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q8 = .ok q16 ∧
      @weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        q1 ap0 = .ok low ∧
      AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q2) ∧
      AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q4) ∧ AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q8) ∧
      AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q12) ∧ AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q16) ∧
      AspisR1S9CurrentFieldOpsV1.Canonical low := by
  obtain ⟨seed, q1, low, hseed, hq1, hlow, hlowCan⟩ :=
    side_zero_scalar_prefix_total ap0 extra hap0 hextra
  have hq1Current : @weights.kpowers currentFieldOps (4#usize) seed = .ok q1 := by
    simpa only [currentFieldOps] using
      (AspisR1S9ConcreteFieldOpsV1.kpowers_concrete_eq_current
        (4#usize) seed).symm.trans hq1
  have hfour : (4#usize).val = 4 := by decide
  obtain ⟨q2, hq2, _⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q1 2#usize
      (by simpa [q1.property, hfour] using (show (2#usize).val < 4 from by decide)))
  have hq2Can := AspisR1S9ScalarFactorKpowersReadV1.kpowers_success_read_current
    seed q1 (hextra 0#usize seed hseed) hq1Current 2#usize q2 hq2
  obtain ⟨q4, hq4, hcan4, _hdec4⟩ :=
    AspisR1S9ConcreteSquareSemanticsV1.concrete_qmSquare_total q2 hq2Can.1
  obtain ⟨q8, hq8, hcan8, _hdec8⟩ :=
    AspisR1S9ConcreteSquareSemanticsV1.concrete_qmSquare_total q4 hcan4
  obtain ⟨q12, hq12, hcan12⟩ :=
    AspisR1S9QMMulTotalCanonicalV1.concrete_qm_mul_total q8 q4 hcan8 hcan4
  obtain ⟨q16, hq16, hcan16, _hdec16⟩ :=
    AspisR1S9ConcreteSquareSemanticsV1.concrete_qmSquare_total q8 hcan8
  exact ⟨seed, q1, q2, q4, q8, q12, q16, low,
    hseed, hq1, hq2, hq4, hq8, hq12, hq16, hlow,
    hq2Can.1, hcan4, hcan8, hcan12, hcan16, hlowCan⟩


#print axioms side_zero_scalar_prefix_total
#print axioms side_zero_high_prefix_total

end AspisR1S9SideZeroHighPrefixTotalityV2
