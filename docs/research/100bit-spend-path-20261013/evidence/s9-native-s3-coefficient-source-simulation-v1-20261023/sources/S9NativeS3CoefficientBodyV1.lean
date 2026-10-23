import S9NativeS3ArithmeticTransportV1
import S9S2CoefficientsCanonicalV1
import S9CandidateUpdateMapV1
import S9ActualDotRangeBoundsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9NativeS3CoefficientBodyV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3FieldReaderV1 (nativeToOld)
open AspisR1S9CandidateFoldMapPrimitivesV1 (mapArray mapArray_index_result)
open AspisR1S9NativeArrayCanonicalV1 (ReadsCanonical)
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev R := core.ops.range.Range Usize
abbrev C := Array W 12#usize

def toOld (c : C) : Array AspisR1GroupedPairActualFieldOpsV3.field.WideExact 12#usize :=
  mapArray nativeToOld c

theorem source_group_tables_same : weights.S2_INACTIVE_GROUPS=
    AspisR1GroupedPairActualFieldOpsV3.weights.S2_INACTIVE_GROUPS := by
  unfold weights.S2_INACTIVE_GROUPS AspisR1GroupedPairActualFieldOpsV3.weights.S2_INACTIVE_GROUPS
  rfl

/-- SAME bounded strict read supplies native canonicality through the already
proved old/current coordinate identity, with no allocation interface premise. -/
theorem native_field_success_canonical_of_fit (f : Slice U8) (j : Usize) (w : W)
    (hfit : (j.val+1)*32 ≤ f.val.length) (h : weights.field f j=.ok w) :
    AspisR1S9ActualPairWideCanonicalV1.Canonical w := by
  change AspisR1CurrentWide.Proof.CanonicalWide (AspisR1S9ActualPairWideCanonicalV1.toCurrent w)
  have hc := (AspisR1S9NativeS3FieldReaderV1.native_field_success_old_reader f j w hfit h).2.1
  change AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toE (nativeToOld w)) at hc
  simpa only [AspisR1S9NativeS3FieldReaderV1.native_current_coordinates] using hc

/-- The SAME native coefficient-body continuation maps to the existing old
S3 body and the SAME mapped output array. Desired old read/add/update success
is derived internally, never assumed. The source64-span bounds rule out the
wrapping-reader counterexample. -/
theorem native_coefficient_cont_old_body (f : Slice U8) (iter iterOut : R) (c out : C)
    (hbytes : 2048 ≤ f.val.length) (hend : iter.end.val ≤ 64)
    (hcan : ReadsCanonical c)
    (hbody : weights.s2_grouped_inactive_pair_loop0.body f iter c=.ok (.cont (iterOut,out))) :
    AspisR1GroupedPairActualFieldOpsV3.weights.s2_grouped_inactive_pair_loop0.body
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actualOperations f iter (toOld c)=
      .ok (.cont (iterOut,toOld out)) := by
  obtain ⟨j,code,group,old,value,total,hn,hcode,hgroup,hold,hfield,hadd,hupdate⟩ :=
    AspisR1S9S2CoefficientsCanonicalV1.body_cont_source f iter iterOut c out hbody
  subst group
  have hj := (AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds iter iterOut j hn).2.1
  have hfit : (j.val+1)*32 ≤ f.val.length := by omega
  have hread := (AspisR1S9NativeS3FieldReaderV1.native_field_success_old_reader f j value hfit hfield).1
  have ho := hcan (UScalar.cast .Usize code) old hold
  have hv := native_field_success_canonical_of_fit f j value hfit hfield
  have hsum := AspisR1S9NativeS3ArithmeticTransportV1.native_add_success_old_operation old value total ho hv hadd
  have holdMap := mapArray_index_result nativeToOld c (UScalar.cast .Usize code)
  rw [hold] at holdMap
  have holdOld : Array.index_usize (toOld c) (UScalar.cast .Usize code)=.ok (nativeToOld old) := holdMap.symm
  have hg := AspisR1S9ConstructorV3Loop2InnerCanonicalV1.index_success_bound c (UScalar.cast .Usize code) old hold
  obtain ⟨outOld,hu,he⟩ := AspisR1S9CandidateUpdateMapV1.mapArray_update_success
    nativeToOld c (UScalar.cast .Usize code) total hg out hupdate
  have huOld : Array.update (toOld c) (UScalar.cast .Usize code) (nativeToOld total)=.ok (toOld out) := by
    rw [←he] at hu
    exact hu
  have hcodeOld : Array.index_usize AspisR1GroupedPairActualFieldOpsV3.weights.S2_INACTIVE_GROUPS
      j=.ok code := by
    rw [←source_group_tables_same]
    exact hcode
  unfold AspisR1GroupedPairActualFieldOpsV3.weights.s2_grouped_inactive_pair_loop0.body
  simp only [hn,bind_tc_ok]
  have htail : (do
      let i ← Array.index_usize AspisR1GroupedPairActualFieldOpsV3.weights.S2_INACTIVE_GROUPS j
      let previous ← Array.index_usize (toOld c) (UScalar.cast .Usize i)
      let input ← AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decodeField f j
      let sum ← AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.add previous input
      let updated ← Array.update (toOld c) (UScalar.cast .Usize i) sum
      Result.ok (ControlFlow.cont (iterOut,updated))) =
      (Result.ok (ControlFlow.cont (iterOut,toOld out)) :
        Result (ControlFlow (R × Array AspisR1GroupedPairActualFieldOpsV3.field.WideExact 12#usize)
          (Array AspisR1GroupedPairActualFieldOpsV3.field.WideExact 12#usize))) := by
    simp only [hcodeOld,bind_tc_ok,holdOld,hread,hsum,huOld]
  exact htail

#print axioms native_field_success_canonical_of_fit
#print axioms source_group_tables_same
#print axioms native_coefficient_cont_old_body
end AspisR1S9NativeS3CoefficientBodyV1
