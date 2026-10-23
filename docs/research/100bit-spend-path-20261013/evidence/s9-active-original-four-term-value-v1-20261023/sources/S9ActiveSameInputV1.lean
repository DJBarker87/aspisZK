import S9NativeS3ZeroPrefixV1
import S9NativeS3WeightBodyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActiveSameInputV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Can decode)
open AspisR1S9NativeS3CoefficientBodyV1 (C)

/-- Actual source active-field success refers to the SAME strict64 input
stream supplied by the SAME accepted inactive coefficient run on f. No new
chosen data vector, dataCan or desired field-value premise is used. -/
theorem actual_field_same_coefficient_input (f : Slice U8) (coefficients : C)
    (hbytes : 2048≤f.val.length)
    (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
      (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients)
    (j : Usize) (value : W) (hj : j.val<64)
    (hfield : weights.field f j=.ok value) : Can value ∧
    decode value=AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff j.val := by
  have hfit : (j.val+1)*32≤f.val.length := by omega
  have hr := AspisR1S9NativeS3FieldReaderV1.native_field_success_old_reader f j value hfit hfield
  obtain ⟨x,hx,hvalue⟩ := (AspisR1S9NativeS3ZeroPrefixV1.native_zero_coefficient_success_prefix
    f coefficients hbytes hcoeff).2.2 j hj
  have he : AspisR1S9NativeS3FieldReaderV1.nativeToOld value=x := Result.ok.inj (hr.1.symm.trans hx)
  refine ⟨AspisR1S9NativeS3CoefficientBodyV1.native_field_success_canonical_of_fit f j value hfit hfield,?_⟩
  change AspisR1CurrentWide.Proof.decodeWide (AspisR1S9ActualPairWideCanonicalV1.toCurrent value)=_
  calc
    AspisR1CurrentWide.Proof.decodeWide (AspisR1S9ActualPairWideCanonicalV1.toCurrent value)=
        AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decode
          (AspisR1S9NativeS3FieldReaderV1.nativeToOld value) := hr.2.2.symm
    _ = AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decode x :=
      congrArg AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decode he
    _ = _ := hvalue

#print axioms actual_field_same_coefficient_input
end AspisR1S9ActiveSameInputV1
