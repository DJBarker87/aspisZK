import V7ProductionCallbacksR30Qm31Canonical

/-! Canonical output of production Karatsuba reconstruction, including the
three-product helper. Wide sums are reduced before field subtraction. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30KaratsubaCanonical
open V7CallerCurrentReleaseR26FieldBridge
open V7ProductionCallbacksR30FieldCanonical
open V7ProductionCallbacksR30Qm31Canonical

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

theorem successful_result_property {T : Type} {computation : Result T}
    {property : T → Prop} {output : T}
    (expected : ∃ value, computation = ok value ∧ property value)
    (run : computation = ok output) : property output := by
  obtain ⟨value, valueRun, valueProperty⟩ := expected
  have exactOutput := Result.ok.inj (run.symm.trans valueRun)
  exact exactOutput ▸ valueProperty

theorem successful_callback_reduce_canonical
    (value : Std.U64) (output : Std.U32)
    (run : V7ProductionCallbacksR29.aspis_core.field.M31.reduce_u64 value = ok output) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 output := by
  have bound : value.val ≤ 18446744073709551615 := by
    have bounds := value.hBounds
    change value.val < 18446744073709551616 at bounds
    omega
  have reduceEq : V7ProductionCallbacksR29.aspis_core.field.M31.reduce_u64 value =
      V7CallerCurrentReleaseR26.field.M31.reduce_u64 value := by
    unfold V7ProductionCallbacksR29.aspis_core.field.M31.reduce_u64
      V7CallerCurrentReleaseR26.field.M31.reduce_u64
    rw [callback_reduce_u64_eq_current_reduce_u64_wide value bound]
  rw [reduceEq] at run
  obtain ⟨expected, expectedRun, canonical, _⟩ :=
    generated_m31_reduce_u64_corresponds value
  have exactOutput := Result.ok.inj (run.symm.trans expectedRun)
  rw [exactOutput]
  exact canonical

theorem successful_channel_closure_canonical
    (sums : Array Std.U64 3#usize) (output : CallbackCM31)
    (run : V7ProductionCallbacksR29.aspis_core.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
      () sums = ok output) : GeneratedCanonicalCM31 output := by
  unfold V7ProductionCallbacksR29.aspis_core.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
    at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨wide0, wide0Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨m0, m0Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨wide1, wide1Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨m1, m1Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨wide2, wide2Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨m2, m2Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨real, realRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨cross, crossRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨imag, imagRun, run⟩ := run
  have can0 := successful_callback_reduce_canonical wide0 m0 m0Run
  have can1 := successful_callback_reduce_canonical wide1 m1 m1Run
  have can2 := successful_callback_reduce_canonical wide2 m2 m2Run
  have realCan := successful_result_property
    (callback_m31_sub_canonical m0 m1 can0 can1) realRun
  have crossCan := successful_result_property
    (callback_m31_sub_canonical m2 m0 can2 can0) crossRun
  have imagCan := successful_result_property
    (callback_m31_sub_canonical cross m1 crossCan can1) imagRun
  have exactOutput := Result.ok.inj run
  cases exactOutput
  exact ⟨realCan, imagCan⟩

theorem successful_channel_sums_canonical
    (sums : Array (Array Std.U64 3#usize) 3#usize) (output : CallbackQM31)
    (run : V7ProductionCallbacksR29.aspis_core.field.qm31_from_karatsuba_channel_sums
      sums = ok output) : GeneratedCanonicalQM31 output := by
  unfold V7ProductionCallbacksR29.aspis_core.field.qm31_from_karatsuba_channel_sums at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨sums0, sums0Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨m0, m0Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨sums1, sums1Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨m1, m1Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨sums2, sums2Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨m2, m2Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨rM1, rM1Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨low, lowRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨cross, crossRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨high, highRun, run⟩ := run
  have can0 := successful_channel_closure_canonical sums0 m0 m0Run
  have can1 := successful_channel_closure_canonical sums1 m1 m1Run
  have can2 := successful_channel_closure_canonical sums2 m2 m2Run
  have rCan := successful_result_property (callback_mul_by_r_canonical m1 can1) rM1Run
  have lowCan := successful_result_property (callback_cm31_add_canonical m0 rM1 can0 rCan) lowRun
  have crossCan := successful_result_property (callback_cm31_sub_canonical m2 m0 can2 can0) crossRun
  have highCan := successful_result_property (callback_cm31_sub_canonical cross m1 crossCan can1) highRun
  have exactOutput := Result.ok.inj run
  cases exactOutput
  exact ⟨lowCan, highCan⟩

/-- Canonicality alone needs no bounds on the accumulated wide channels:
every returned channel is reduced before the final field operations. This
theorem makes no claim about dot-product semantics or absence of overflow. -/
theorem successful_prepared_sum_products3_canonical
    (left : Array CallbackPreparedQM31 3#usize)
    (right : Array CallbackQM31 3#usize) (output : CallbackQM31)
    (run : V7ProductionCallbacksR29.aspis_core.field.qm31_sum_products3_prepared
      left right = ok output) : GeneratedCanonicalQM31 output := by
  unfold V7ProductionCallbacksR29.aspis_core.field.qm31_sum_products3_prepared at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨sums, sumsRun, run⟩ := run
  exact successful_channel_sums_canonical sums output run

#print axioms successful_callback_reduce_canonical
#print axioms successful_channel_closure_canonical
#print axioms successful_channel_sums_canonical
#print axioms successful_prepared_sum_products3_canonical
end V7ProductionCallbacksR30KaratsubaCanonical
