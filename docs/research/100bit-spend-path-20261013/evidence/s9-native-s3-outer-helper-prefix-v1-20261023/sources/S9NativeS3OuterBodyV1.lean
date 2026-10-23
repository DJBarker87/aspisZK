import S9NativeS3WeightLoopV1
import S9NativeS3ZeroPrefixV1
import S9S2InactiveCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativeS3OuterBodyV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W R Low Can decode)
open AspisR1S9NativeS3WeightLoopV1 (sourceMask actualSelectedPrefix)
abbrev Coefficients := Array W 12#usize

theorem native_zero_decode : decode aspis_core.field.wide_exact.WideExact.ZERO=0 := by
  have hz := AspisR1GroupedPairActualFieldOpsV3.NativeZeroReadbackReuseV1.zero_seed_decode
  change AspisR1CurrentWide.Proof.decodeWide
    (AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toE
      AspisR1GroupedPairActualFieldOpsV3.field.WideExact.ZERO)=0 at hz
  rw [←AspisR1S9NativeS3ZeroPrefixV1.native_zero_value_maps,
    AspisR1S9NativeS3FieldReaderV1.native_current_coordinates] at hz
  exact hz

/-- SAME actual outer12 continuation supplies its real inner16 run and
coefficient/product/add events. Their previously proved meanings determine
the native output increment; no inner-weight or product meaning is assumed. -/
theorem native_outer_cont_decoded (low : Low) (coefficients : Coefficients)
    (iter iterOut : R) (pair out : W) (hend : iter.end.val≤12)
    (hlow : AspisR1S9NativeArrayCanonicalV1.ReadsCanonical low)
    (hcoeff : AspisR1S9NativeArrayCanonicalV1.ReadsCanonical coefficients) (hpair : Can pair)
    (hbody : weights.s2_grouped_inactive_pair_loop1.body low coefficients iter pair=
      .ok (.cont (iterOut,out))) :
    ∃ (group : Usize) (coefficient : W),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some group,iterOut) ∧
      Array.index_usize coefficients group=.ok coefficient ∧ group.val<12 ∧ Can out ∧
      decode out=decode pair+decode coefficient*
        actualSelectedPrefix (sourceMask group).val 16 (low.val.map decode) := by
  obtain ⟨group,weight,coefficient,product,hn,hinner,hcoefficient,hmul,hadd⟩ :=
    AspisR1S9S2InactiveCanonicalV1.outer_body_cont_source low coefficients iter iterOut pair out hbody
  have hg := (AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds iter iterOut group hn).2.1
  have hg12 : group.val<12 := by omega
  obtain ⟨cweight,hweight⟩ := AspisR1S9NativeS3WeightLoopV1.native_weight_loop_selected_prefix
    low group aspis_core.field.wide_exact.WideExact.ZERO weight hlow
    AspisR1S9ActualPairWideOutputCanonicalV1.zero_canonical hinner
  rw [native_zero_decode,zero_add] at hweight
  obtain ⟨cproduct,hproduct⟩ := AspisR1S9NativeWideDecodedArithmeticV1.actual_mul_success_decoded
    coefficient weight product (hcoeff group coefficient hcoefficient) cweight hmul
  obtain ⟨cout,hout⟩ := AspisR1S9NativeWideDecodedArithmeticV1.actual_add_success_decoded
    pair product out hpair cproduct hadd
  rw [hproduct] at hout
  change decode out=decode pair+decode coefficient*decode weight at hout
  rw [hweight] at hout
  exact ⟨group,coefficient,hn,hcoefficient,hg12,cout,hout⟩

#print axioms native_zero_decode
#print axioms native_outer_cont_decoded
end AspisR1S9NativeS3OuterBodyV1
