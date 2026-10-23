import S9NativeS3OuterLoopV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativeS3HelperPrefixV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Low Can decode)
open AspisR1S9NativeS3OuterBodyV1 (Coefficients)
open AspisR1S9NativeS3CoefficientBodyV1 (toOld)
open AspisR1S9NativeS3FieldReaderV1 (nativeToOld)
open AspisR1S9CandidateFoldMapPrimitivesV1 (mapArray_index_result)

theorem mapped_coefficients_canonical_native (coefficients : Coefficients)
    (hc : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.CanonicalAccumulatorArray (toOld coefficients)) :
    AspisR1S9NativeArrayCanonicalV1.ReadsCanonical coefficients := by
  intro i value hread
  have hi := AspisR1S9ConstructorV3Loop2InnerCanonicalV1.index_success_bound coefficients i value hread
  let k : Fin 12 := ⟨i.val,by simpa using hi⟩
  have hpoint := hc k
  have hm := mapArray_index_result nativeToOld coefficients i
  rw [hread] at hm
  have hreadOld : Array.index_usize (toOld coefficients) i=.ok (nativeToOld value) := hm.symm
  have hv := AspisR1S9FactorArrayEntryV1.accepted_index_eq_atN
    (toOld coefficients) i hi (nativeToOld value) hreadOld
  change AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical
    (AspisR1S9FactorArrayEntryV1.atN (toOld coefficients) i hi) at hpoint
  rw [←hv] at hpoint
  change AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toE (nativeToOld value)) at hpoint
  change AspisR1CurrentWide.Proof.CanonicalWide (AspisR1S9ActualPairWideCanonicalV1.toCurrent value)
  simpa only [AspisR1S9NativeS3FieldReaderV1.native_current_coordinates] using hpoint

private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m;next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- SAME actual optimised helper provides its own zero-seeded coefficients,
all64reader semantics, coefficient Can and outer12 run. The selected outer
product prefix is for THAT SAME array and actual output; no coefficient/inner
meaning or child event is independently supplied. -/
theorem native_helper_success_joint_prefix (f : Slice U8) (low : Low) (out : W)
    (hbytes : 2048 ≤ f.val.length)
    (hlow : AspisR1S9NativeArrayCanonicalV1.ReadsCanonical low)
    (h : weights.s2_grouped_inactive_pair f low=.ok out) :
    ∃ (coefficients : Coefficients)
      (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
        (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients),
      AspisR1S9NativeArrayCanonicalV1.ReadsCanonical coefficients ∧
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.DecodedMeaning (toOld coefficients)
        (AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.PrefixMeaning
          (AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff) (fun _ => 0) 64) ∧
      weights.s2_grouped_inactive_pair_loop1 {start:=0#usize,«end»:=12#usize} low coefficients
        aspis_core.field.wide_exact.WideExact.ZERO=.ok out ∧
      Can out ∧ decode out=AspisR1S9NativeS3OuterLoopV1.outerPrefix low coefficients 12 := by
  unfold weights.s2_grouped_inactive_pair at h
  obtain ⟨coefficients,hcoeff,houter⟩ := bind_success _ _ _ h
  have hprefix := AspisR1S9NativeS3ZeroPrefixV1.native_zero_coefficient_success_prefix
    f coefficients hbytes hcoeff
  have ccoeff := mapped_coefficients_canonical_native coefficients hprefix.2.1
  obtain ⟨cout,hvalue⟩ := AspisR1S9NativeS3OuterLoopV1.native_outer_loop_prefix
    low coefficients aspis_core.field.wide_exact.WideExact.ZERO out hlow ccoeff
    AspisR1S9ActualPairWideOutputCanonicalV1.zero_canonical houter
  rw [AspisR1S9NativeS3OuterBodyV1.native_zero_decode,zero_add] at hvalue
  exact ⟨coefficients,hcoeff,ccoeff,hprefix.1,houter,cout,hvalue⟩

#print axioms mapped_coefficients_canonical_native
#print axioms native_helper_success_joint_prefix
end AspisR1S9NativeS3HelperPrefixV1
