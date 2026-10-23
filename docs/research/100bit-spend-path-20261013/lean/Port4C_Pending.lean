import Port3_Parents
import Port3_NativeQueryTerms

/-! Both query blocks use this same native constructor. No second Vec or
independent successful reservation is introduced. Allocation/Copy retain the
existing TrustedStd interpretation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_Pending
open Aeneas Aeneas.Std Result AspisR1Stage2
variable {CoreError W : Type}

theorem installed_result (base : VTop_Stages.Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError)
    (query : Port3_NativeQueryBody.Ops)
    (finish : Stage2Finish.FinishOps W)
    (weights : Slice aspis_core.field.QM31) (size : weights.val.length=64) :
    (Port3_Parents.installed base reserved batch geometry query finish).op10 weights =
      if reserved then ok (.Ok ⟨Port3_PendingInstall.raw weights,0#usize⟩)
      else ok (.Err .Allocation) := by
  change Port3_NativePendingInstall.source reserved weights = _
  rw [Port3_NativePendingInstall.reference_eq reserved weights size,
    Port3_PendingInstall.pending_exact]

/-- Same call, all raw rows, initial trace and progress. Applies unchanged to
TX1's initial weights and TX2's decoded checkpoint weights. -/
theorem accepted (reserved : Bool) (weights : Slice aspis_core.field.QM31)
    (state : verifier.BatchedWeights) (size : weights.val.length=64)
    (h : Port3_NativePendingInstall.source reserved weights=ok (.Ok state)) :
    reserved=true ∧ state.raw.val=weights.val.map Port3_PendingInstall.row ∧
    state.terms=0#usize ∧ state.raw.val.length=64 ∧
    S7Kani3CallerTrace.PushTrace (Port3_PendingInstall.owned weights)
      (⟨state.raw,state.terms⟩ : S7Kani2AccumulatorLoop.BatchedWeights)
      (S7Kani3CallerTrace.initialSum (Port3_PendingInstall.owned weights)) ∧
    S7JoinRowsTrace.Progress 0 0
      (⟨state.raw,state.terms⟩ : S7Kani2AccumulatorLoop.BatchedWeights) := by
  have fields := Port3_NativePendingInstall.accepted_fields reserved weights state size h
  rw [Port3_NativePendingInstall.reference_eq reserved weights size] at h
  exact ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,
    Port3_PendingInstall.accepted_trace reserved weights state h,
    Port3_PendingInstall.accepted_progress reserved weights state size h⟩

#print axioms installed_result
#print axioms accepted
end AspisR1.Port4C_Pending
end
