import S9NativeS3ExistingPrefixV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativeS3SourceRowV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Low Can decode)
open AspisR1S9NativeS3OuterBodyV1 (Coefficients)
open AspisR1S9NativeS3CoefficientBodyV1 (toOld)
open AspisR1S9NativeS3ExistingPrefixV1 (toOldLow)
open AspisR1.S3S9CurrentSourceModel

/-- The SAME native accepted optimized helper equals the existing protocol
inactive-row functional. Coefficients, their strict-reader input stream and
all inner/outer source runs are derived from this single call. -/
theorem native_helper_success_source_row (f : Slice U8) (low : Low) (out : W)
    (hbytes : 2048 ≤ f.val.length)
    (hlow : AspisR1S9NativeArrayCanonicalV1.ReadsCanonical low)
    (h : weights.s2_grouped_inactive_pair f low=.ok out) :
    ∃ (coefficients : Coefficients)
      (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
        (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients),
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.DecodedMeaning (toOld coefficients)
        (AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.PrefixMeaning
          (AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff) (fun _ => 0) 64) ∧
      Can out ∧ decode out=ungroupedPair
        (fun j => AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff j.val)
        (fun s => (low.val.map decode).getD s.val 0) inactiveAtSource := by
  obtain ⟨coefficients,hcoeff,_,hmeaning,_,cout,hvalue⟩ :=
    AspisR1S9NativeS3HelperPrefixV1.native_helper_success_joint_prefix f low out hbytes hlow h
  let input := AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff
  have hp := AspisR1GroupedPairActualFieldOpsV3.ActualGroupedPairPrefixFormula.actual_outer_prefix_eq_parser_grouped_prefix
    (toOldLow low) (toOld coefficients) input hmeaning
  have hg := AspisR1GroupedPairActualFieldOpsV3.ActualGroupedPairSourceRow.parserGroupedPrefix_eq_source_groupedPair
    (toOldLow low) input
  change _=groupedPair (fun j=>input j.val)
    (fun s=>((toOldLow low).val.map AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decode).getD s.val 0)
    groupAt inactiveAtGroup at hg
  have hl := AspisR1S9NativeS3ExistingPrefixV1.mapped_decoded_list low
  change (toOldLow low).val.map AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decode=
    low.val.map decode at hl
  rw [hl] at hg
  rw [AspisR1S9NativeS3ExistingPrefixV1.outer_prefix_same low coefficients 12 le_rfl,hp,hg] at hvalue
  rw [s3_grouped_pair_exact] at hvalue
  exact ⟨coefficients,hcoeff,hmeaning,cout,hvalue⟩

#print axioms native_helper_success_source_row
end AspisR1S9NativeS3SourceRowV1
