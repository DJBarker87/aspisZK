import S9ActualPairHelperOriginalCoefficientsV1
import S9ConcreteScalarFactorBridgeV1
import S3S9TransparentFoldS2InstanceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualScalarFourTermMeaningV1
open AspisR1S9ActualPairScalarCallbackV1
open AspisR1S9ActualPairHelperOriginalCoefficientsV1
abbrev HW := AspisR1S9HelperP6.field.WideExact
abbrev HQ := AspisR1S9HelperP6.field.QM31
abbrev U := Usize
abbrev E := AspisWideTower.WideExact
abbrev QCanonical := AspisR1S9ActualPairQMHelperTransportV1.Canonical
def GoodQArray (f : Array Q 4#usize) : Prop :=
  ∀ (i : Usize) (q : Q), Array.index_usize f i=.ok q → QCanonical q
abbrev contribution := AspisR1S9ScalarFactorFourFoldMeaningV1.contribution
def decodeNative (x : W) : E := AspisR1CurrentWide.Proof.decodeWide
  (AspisR1S9ActualPairWideCanonicalV1.toCurrent x)

theorem mapped_native_decode (x : W) :
    AspisR1S9CurrentFieldOpsV1.decode (toHelperW x)=decodeNative x := by
  change AspisR1CurrentWide.Proof.decodeWide
    (AspisR1S9CurrentFieldOpsV1.toE (AspisR1S9CurrentFieldOpsV1.fromE
      (AspisR1S9ActualPairWideCanonicalV1.toCurrent x)))=decodeNative x
  rw [AspisR1S9CurrentFieldOpsV1.to_from]
  rfl

/-- Native SAME-call four-term PERM/quarter equation. Concrete iterator/zero
and arithmetic semantics are the existing proved instances, not premises. -/
theorem actual_scalar_success_four_term_meaning
    (f : Array Q 4#usize) (p : Array W 4#usize) (out : W)
    (hp : GoodArray p) (hf : GoodQArray f)
    (hcall : AspisR1S9ProductionPairCutV1.weights.Weights.scalar_factor f p=.ok out) :
    ∃ (we : HW) (j0 j1 j2 j3 : U)
      (p0 p1 p2 p3 : HW) (q0 q1 q2 q3 : HQ),
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1S9CurrentFieldOpsV1.toE we) ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 0#usize = .ok j0 ∧
      Array.index_usize (mapArray toHelperW p) j0 = .ok p0 ∧ Array.index_usize (mapArray toHelperQ f) 0#usize = .ok q0 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 1#usize = .ok j1 ∧
      Array.index_usize (mapArray toHelperW p) j1 = .ok p1 ∧ Array.index_usize (mapArray toHelperQ f) 1#usize = .ok q1 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 2#usize = .ok j2 ∧
      Array.index_usize (mapArray toHelperW p) j2 = .ok p2 ∧ Array.index_usize (mapArray toHelperQ f) 2#usize = .ok q2 ∧
      Array.index_usize AspisR1S9HelperP6.weights.PERM 3#usize = .ok j3 ∧
      Array.index_usize (mapArray toHelperW p) j3 = .ok p3 ∧ Array.index_usize (mapArray toHelperQ f) 3#usize = .ok q3 ∧
      decodeNative out = (((((0 : E) +
        AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p0 q0) +
        AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p1 q1) +
        AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p2 q2) +
        AspisR1S9ScalarFactorFourFoldMeaningV1.contribution p3 q3) *
          AspisR1CurrentWide.Proof.wideScalarEmbedding
            AspisR1S9HelperP6.weights.QUARTER := by
  obtain ⟨hout,hhelper⟩ := AspisR1S9ActualPairScalarFactorShortV1.actual_scalar_factor_success_maps
    f p out hp hcall
  have hinstalled : (letI : AspisR1S9HelperP6.FieldOps :=
      AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps
        (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
          AspisR1S9ConcreteFieldOpsV1.concreteFieldOps)
      AspisR1S9HelperP6.weights.Weights.scalar_factor
        (mapArray toHelperQ f) (mapArray toHelperW p))=.ok (toHelperW out) := by
    rw [AspisR1S9ConcreteScalarFactorBridgeV1.concrete_factor_ops_eq]
    exact hhelper
  have hpvalues : ∀ i x, Array.index_usize (mapArray toHelperW p) i=.ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x := by
    intro i x hr
    obtain ⟨v,hv,he⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv
      toHelperW p i x hr
    rw [←he]
    exact native_w_canonical v (hp i v hv)
  have hqvalues : ∀ i x, Array.index_usize (mapArray toHelperQ f) i=.ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x) := by
    intro i x hr
    obtain ⟨v,hv,he⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv
      toHelperQ f i x hr
    rw [←he]
    exact native_q_canonical v (hf i v hv)
  have hm := AspisR1S9TransparentFoldS2InstanceV1.scalar_factor_success_general_source_formula
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
    (mapArray toHelperW p) (mapArray toHelperQ f) (toHelperW out)
    hinstalled hpvalues hqvalues
  rw [mapped_native_decode out] at hm
  exact hm

#print axioms mapped_native_decode
#print axioms actual_scalar_success_four_term_meaning
end AspisR1S9ActualScalarFourTermMeaningV1
