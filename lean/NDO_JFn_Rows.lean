import NDO_JFn_PendingHistory
import NDO_JFn_AccumulatorCanonical
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Rows
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem power : S7JoinBackendCarriers.Canonical (Port3_RowsInstall.toK JFo_Prepared.accumulator.power) := by
  intro j
  fin_cases j
  · change 1007926423<2147483647;omega
  · change 526023474<2147483647;omega
  · change 347718395<2147483647;omega
  · change 268326460<2147483647;omega

/-- All64 actual row writes for the first remaining TX2 query, from the
actual decoded checkpoint weights and constructed pending state. Geometry's
basis is still supplied; no row-success or push-history premise is assumed. -/
theorem source (seed : Port3_NativeQueryBody.Ops) (basis : Array U32 256#usize)
    (canonical : S7JoinBasisCanonical.Canonical basis) :
    ∃ after sumOut,
      Port3_NativeQueryBody.verifier.accumulate_batched_with_node_loop1
        (JFn_ArrayBuilder.ops seed) {start:=0#usize,«end»:=64#usize}
        JFo_Prepared.accumulator.weights JFo_Prepared.accumulator.power JFo_Prepared.accumulator.next
        JFo_Pending.value 64#usize basis=ok (Port3_RowsInstall.fromBW after) ∧
      S7Kani3CallerTrace.PushTrace JFn_PendingHistory.old after sumOut ∧
      S7JoinRowsTrace.Progress 0 64 after := by
  obtain ⟨after,sumOut,run,trace,progress,_⟩ := Port4C_RowMeaning.rows
    (Port5Q1_QueryPorts.install (SAQ_Decoder.install seed)) JFn_PendingHistory.old
    JFo_Prepared.accumulator.weights JFo_Pending.value JFn_PendingHistory.sum basis
    JFo_Prepared.accumulator.power JFo_Prepared.accumulator.next 0
    JFo_Prepared.weights_length (by change 10≤22;omega) power canonical
    JFn_PendingHistory.trace JFn_PendingHistory.progress
  exact ⟨after,sumOut,run,trace,progress⟩

#print axioms power
#print axioms source
end AspisR1.JFn_Rows
end
