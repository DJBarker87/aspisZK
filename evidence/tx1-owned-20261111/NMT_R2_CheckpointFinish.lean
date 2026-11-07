import NMT_R2_CheckpointEquation
import NMT_R2_Observation
import NMT_345ScalarSize
set_option autoImplicit false
noncomputable section
namespace NMT_R2_CheckpointFinish
open Aeneas Aeneas.Std NMT_345 RSL NMT_345Observation NMT_R2_Observation NMT_R2_EmittedData NMT_R2_CheckpointEquation

theorem finish_observe (r : core.result.Result Usize OldPE) :
 observe id (mapOuter (mapCore id fromPE) (finish r)) =
 tryObs (observe (fun n : Usize => n.val) (mapOuter (mapCore id fromPE) (.ok r)))
  (fun n => check (n != CHECKPOINT_BYTES) .invalidAccountData) := by
 cases r with
 | Err e => rfl
 | Ok n =>
  change observe id (mapOuter (mapCore id fromPE)
   (if n != 1768#usize then .ok (.Err .InvalidAccountData) else .ok (.Ok ()))) =
   check (n.val != CHECKPOINT_BYTES) .invalidAccountData
  rw [scalar_size_compare]
  cases h : n != 1768#usize <;> rfl

theorem length_continue (r : Result (core.result.Result Usize OldPE)) :
 observe id (mapOuter (mapCore id fromPE) (r >>= finish)) =
 tryObs (observe (fun n : Usize => n.val) (mapOuter (mapCore id fromPE) r))
  (fun n => check (n != CHECKPOINT_BYTES) .invalidAccountData) := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok value => exact finish_observe value
#print axioms finish_observe
#print axioms length_continue
end NMT_R2_CheckpointFinish
end
