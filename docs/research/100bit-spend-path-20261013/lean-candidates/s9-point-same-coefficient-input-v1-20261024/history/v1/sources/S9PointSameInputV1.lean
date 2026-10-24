import S9ActiveSameInputV1
import S9SharedSumObservationsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9PointSameInputV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3CoefficientBodyV1 (C)
open AspisR1S9SharedSumObservationsV1 (fieldValue finIndex finIndex_val)
namespace Old := AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
namespace S5 := AspisR1S5PairCutTransparentReaderV1
namespace Bounded := AspisR1S9NativeFieldS5BoundedReaderV1
namespace Port := AspisR1S5PairCutFieldCallbackV1
abbrev W := aspis_core.field.wide_exact.WideExact

/-- An actual successful strict old read implies success of the SAME native
reader in its proven fitting-window domain, via the already proved full
Result reader transport. No decoder or native-field success is assumed. -/
theorem old_read_native_success (f : Slice U8) (j : Usize) (x : Old.S)
    (hfit : (j.val+1)*32≤f.val.length)
    (hold : Old.decodeField f j=.ok x) : ∃ value : W, weights.field f j=.ok value := by
  unfold Old.decodeField at hold
  cases hf : AspisR1CurrentWide.Proof.finishField f j with
  | fail e => simp only [hf,bind_tc_fail] at hold; cases hold
  | div => simp only [hf,bind_tc_div] at hold; cases hold
  | ok value =>
    have hs : S5.readerBody S5.actualPairDecoder f j=.ok (Port.finishToPair value) := by
      rw [S5.actualReader_eq_checkedCallback]
      simp only [Port.checkedFieldCallback,hf,bind_tc_ok]
    have hm := Bounded.native_field_maps_s5_reader f j (Bounded.fitting_window_safe f j hfit)
    rw [hs] at hm
    cases hn : weights.field f j with
    | fail e => simp only [hn,AspisR1S9OwnedFromLimbsMapV1.mapResult] at hm; cases hm
    | div => simp only [hn,AspisR1S9OwnedFromLimbsMapV1.mapResult] at hm; cases hm
    | ok result => exact ⟨result,rfl⟩

/-- The accepted zero-seeded native coefficient loop itself produces every
native source field success and its SAME strict-input decoded value. -/
theorem coefficient_run_native_read (f : Slice U8) (coefficients : C)
    (hbytes : 2048≤f.val.length)
    (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
      (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients)
    (j : Usize) (hj : j.val<64) :
    ∃ value : W, weights.field f j=.ok value ∧
      AspisR1S9NativeS3WeightBodyV1.decode value=
        AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff j.val := by
  obtain ⟨old,hold,hmeaning⟩ :=
    (AspisR1S9NativeS3ZeroPrefixV1.native_zero_coefficient_success_prefix
      f coefficients hbytes hcoeff).2.2 j hj
  have hfit : (j.val+1)*32≤f.val.length := by omega
  obtain ⟨value,hfield⟩ := old_read_native_success f j old hfit hold
  exact ⟨value,hfield,(AspisR1S9ActiveSameInputV1.actual_field_same_coefficient_input
    f coefficients hbytes hcoeff j value hj hfield).2⟩

/-- Point sums observe the SAME strict successfulInput as inactive/active
source parts, at EVERY Fin64 position. The actual source reader successes
are derived from the coefficient run, not supplied as desired operands. -/
theorem point_fieldValue_same_input (f : Slice U8) (coefficients : C)
    (hbytes : 2048≤f.val.length)
    (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
      (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients)
    (h64 : 64≤64) (i : Fin 64) :
    fieldValue f (finIndex h64 i)=
      AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff i.val := by
  have hj : (finIndex h64 i).val<64 := by simpa only [finIndex_val] using i.isLt
  obtain ⟨value,hfield,hvalue⟩ := coefficient_run_native_read
    f coefficients hbytes hcoeff (finIndex h64 i) hj
  unfold fieldValue
  rw [hfield]
  have hd : AspisR1S9NativeDecodedScalarProductV1.decodeNative value=
      AspisR1S9NativeS3WeightBodyV1.decode value := rfl
  exact hd.trans (by simpa only [finIndex_val] using hvalue)

#print axioms old_read_native_success
#print axioms coefficient_run_native_read
#print axioms point_fieldValue_same_input
end AspisR1S9PointSameInputV1
