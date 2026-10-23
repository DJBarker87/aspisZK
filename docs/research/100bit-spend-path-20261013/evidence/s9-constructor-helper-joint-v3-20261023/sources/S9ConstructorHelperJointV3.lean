import S9ConstructorPairExtraContractV3
import S9PairTwoBodyCanonicalStatesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorHelperJointV3
open AspisR1S9PairTwoBodyCanonicalStatesV1
open AspisR1S9ActualWeightsNewExtraCurrentCanonicalV3
open AspisR1S9ConstructorPairExtraContractV3

theorem constructor_helper_output_canonical
    (variant : AspisR1S9ActualWeightsNewBoxNewV3.Variant)
    (alpha : Array AspisR1S9ActualWeightsNewBoxNewV3.field.QM31 10#usize)
    (z : Array AspisR1S9ActualWeightsNewBoxNewV3.circle.SecureCirclePoint 2#usize)
    (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights)
    (ap0 ap1 output : PairArray)
    (hnew : AspisR1S9ActualWeightsNewBoxNewV3.weights_new variant alpha z =
      .ok (core.result.Result.Ok w))
    (halpha : ∀ (i : Usize) (q : AspisR1S9PairCallerStepV1.field.QM31),
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray candidateToPairQM alpha) i = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
          (AspisR1S9PairCallerStepV1.toP6Q q)))
    (hhelper : AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights
      ap0 ap1 (pairExtra w) = .ok output)
    (hap0 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW ap0)) j = .ok v → Canonical v)
    (hap1 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW ap1)) j = .ok v →
        AspisR1S9HighTermsTraceV1.canonicalW v) :
    ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW output)) j = .ok v →
      Canonical v := by
  have hextra := constructor_v3_extra_supplies_pair_contract variant alpha z w hnew halpha
  obtain ⟨iter1,iter2,middle,hnext0,hbody0,hactive0,hmiddle,hnext1,hstart1,
      hbody1,hactive1,houtput⟩ :=
    successful_pair_helper_two_body_states_canonical
      ap0 ap1 (pairExtra w) output hhelper hap0 hap1 hextra
  exact houtput

#print axioms constructor_helper_output_canonical
end AspisR1S9ConstructorHelperJointV3
