import S3PowersLowEntryCanonicalV2
import S3ActualLoop1PrefixV5

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S3PowersLowActualCanonicalV1

open AspisR1S3PowersLowEntryCanonicalV1
open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

abbrev S := AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.S
abbrev Canonical := AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical
abbrev LowInputs := AspisR1S3PowersLowEntryCanonicalV1.LowInputs

/-- The low-table callback used by the stateful P6 array model. Its operation
is exactly the previously checked lowStep; the cursor is the generated
from_fn index. -/
def generatedLowCallback (s : AspisR1CurrentWide.field.M31) :
    core.ops.function.FnMut LowInputs Usize S := {
  FnOnceInst := {
    call_once := fun state i => do
      let (value, _) ← AspisR1S3PowersLowEntryCanonicalV1.lowStep s state i.val
      .ok value
  }
  call_mut := fun state i =>
    AspisR1S3PowersLowEntryCanonicalV1.lowStep s state i.val
}

def lowP6StateOK (state : LowInputs × Usize) (_index : Nat) : Prop :=
  AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical state.1

theorem lowP6FnMutStep_success_preserves
    (s : AspisR1CurrentWide.field.M31)
    (state : LowInputs × Usize) (index : Nat) (value : S)
    (next : LowInputs × Usize)
    (hstate : lowP6StateOK state index)
    (hstep : AspisR1FromFnP6Generated.fnMutStep
      (generatedLowCallback s) state index = .ok (value, next)) :
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical value ∧
      lowP6StateOK next (index + 1) := by
  rcases state with ⟨inputState, cursor⟩
  change AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical inputState at hstate
  unfold AspisR1FromFnP6Generated.fnMutStep generatedLowCallback at hstep
  cases hl : AspisR1S3PowersLowEntryCanonicalV1.lowStep s inputState cursor.val with
  | fail e => simp only [hl, bind_tc_fail] at hstep; cases hstep
  | div => simp only [hl, bind_tc_div] at hstep; cases hstep
  | ok pair =>
      rcases pair with ⟨out, nextInput⟩
      cases hc : cursor + 1#usize with
      | fail e => simp only [hl, bind_tc_ok, hc, bind_tc_fail] at hstep; cases hstep
      | div => simp only [hl, bind_tc_ok, hc, bind_tc_div] at hstep; cases hstep
      | ok nextCursor =>
          simp only [hl, bind_tc_ok, hc, bind_tc_ok] at hstep
          have hp := Result.ok.inj hstep
          rcases Prod.mk.inj hp with ⟨hout, hnext⟩
          cases hout
          cases hnext
          have hlow := AspisR1S3PowersLowEntryCanonicalV1.lowStep_success_preserves
            hstate hl
          exact hlow

theorem p6_generated_low_array_success_canonical
    (s : AspisR1CurrentWide.field.M31)
    (inputs : LowInputs)
    (low : Aeneas.Std.Array S (16#usize))
    (final : LowInputs × Usize)
    (hinputs : AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical inputs)
    (hrun : AspisR1FromFnP6Generated.core.array.from_fn_model (16#usize)
      (generatedLowCallback s) inputs = .ok (low, final)) :
    AspisR1GroupedPairActualFieldOpsV3.ActualLoop1.CanonicalLow low := by
  have htrace := AspisR1FromFnP6Generated.core_array_from_fn_model_success_trace
    (16#usize) (generatedLowCallback s) inputs hrun
  have hinitial : lowP6StateOK (inputs, 0#usize) 0 := hinputs
  have hpres := AspisR1FromFnP6.statefulFromFnTrace_preserves
    (lowP6StateOK) AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical
    (by
      intro state i out next hs hstep
      exact lowP6FnMutStep_success_preserves s state i out next hs hstep)
    hinitial htrace
  intro i
  have hmem : low.val[i.val]'(by
      have hp := low.property
      change low.val.length = 16 at hp
      omega) ∈ low.val := by
    exact List.getElem_mem (l := low.val) (n := i.val) (by
      have hp := low.property
      change low.val.length = 16 at hp
      omega)
  exact hpres.1 _ hmem

theorem p6_generated_power_arrays_to_canonical_low
    (x0 x1 : AspisR1PowersConcreteMul.CallbackWide)
    (powers0 : Aeneas.Std.Array AspisR1PowersConcreteMul.CallbackWide (4#usize))
    (powers1 : Aeneas.Std.Array AspisR1PowersConcreteMul.CallbackWide (4#usize))
    (powerFinal0 powerFinal1 :
      AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize) × Usize)
    (s : AspisR1CurrentWide.field.M31)
    (low : Aeneas.Std.Array S (16#usize))
    (lowFinal : LowInputs × Usize)
    (hx0 : AspisR1PowersConcreteMul.Canonical x0)
    (hx1 : AspisR1PowersConcreteMul.Canonical x1)
    (hrun0 : AspisR1FromFnP6Generated.core.array.from_fn_model (4#usize)
      (generatedPowerCallback (4#usize))
      (AspisR1CurrentPowers.field.WideExact.ONE, x0) = .ok (powers0, powerFinal0))
    (hrun1 : AspisR1FromFnP6Generated.core.array.from_fn_model (4#usize)
      (generatedPowerCallback (4#usize))
      (AspisR1CurrentPowers.field.WideExact.ONE, x1) = .ok (powers1, powerFinal1))
    (hlow : AspisR1FromFnP6Generated.core.array.from_fn_model (16#usize)
      (generatedLowCallback s) (powers0.val, powers1.val) = .ok (low, lowFinal)) :
    AspisR1GroupedPairActualFieldOpsV3.ActualLoop1.CanonicalLow low := by
  have hcan0 := AspisR1S3PowersLowEntryCanonicalV1.p6_generated_powers_array_success_canonical
    x0 powers0 powerFinal0 hx0 hrun0
  have hcan1 := AspisR1S3PowersLowEntryCanonicalV1.p6_generated_powers_array_success_canonical
    x1 powers1 powerFinal1 hx1 hrun1
  have hlen0 : powers0.val.length = 4 := by
    have htrace := AspisR1FromFnP6Generated.core_array_from_fn_model_success_trace
      (4#usize) (generatedPowerCallback (4#usize))
      (AspisR1CurrentPowers.field.WideExact.ONE, x0) hrun0
    have hlen := AspisR1FromFnP6.statefulFromFnTrace_length htrace
    have hfour : (4#usize).val = 4 := by decide
    simpa [hfour] using hlen
  have hlen1 : powers1.val.length = 4 := by
    have htrace := AspisR1FromFnP6Generated.core_array_from_fn_model_success_trace
      (4#usize) (generatedPowerCallback (4#usize))
      (AspisR1CurrentPowers.field.WideExact.ONE, x1) hrun1
    have hlen := AspisR1FromFnP6.statefulFromFnTrace_length htrace
    have hfour : (4#usize).val = 4 := by decide
    simpa [hfour] using hlen
  have hcanList0 : AspisR1S3PowersLowEntryCanonicalV1.callbackCanonical powers0.val := by
    intro i hi
    have hmem : powers0.val[i]'(by omega) ∈ powers0.val :=
      List.getElem_mem (l := powers0.val) (n := i) (by omega)
    exact ⟨powers0.val[i]'(by omega), List.getElem?_eq_getElem (by omega), hcan0 _ hmem⟩
  have hcanList1 : AspisR1S3PowersLowEntryCanonicalV1.callbackCanonical powers1.val := by
    intro i hi
    have hmem : powers1.val[i]'(by omega) ∈ powers1.val :=
      List.getElem_mem (l := powers1.val) (n := i) (by omega)
    exact ⟨powers1.val[i]'(by omega), List.getElem?_eq_getElem (by omega), hcan1 _ hmem⟩
  have hinputs : AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical
      (powers0.val, powers1.val) := ⟨hlen0, hlen1, hcanList0, hcanList1⟩
  exact p6_generated_low_array_success_canonical s (powers0.val, powers1.val)
    low lowFinal hinputs hlow

#print axioms lowP6FnMutStep_success_preserves
#print axioms p6_generated_low_array_success_canonical
#print axioms p6_generated_power_arrays_to_canonical_low

end AspisR1S3PowersLowActualCanonicalV1
