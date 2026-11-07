import NKF_CheckpointBox
set_option autoImplicit false
noncomputable section
namespace NMX_CheckpointValue
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

def raw (b : Slice U8) : core.result.Result NJQ_Carrier.C NJQ_Carrier.F :=
 if size : b.val.length = 192 then NJQ_CheckpointCut.pipeline b size
 else .Err .WrongLength

def decoded (b : Slice U8) := NKF_BoxModel.tail (NJQ_Carrier.checkpoint_result (raw b))

theorem source (b : Slice U8) : NKF_CheckpointBox.reference b = ok (decoded b) := by
 unfold NKF_CheckpointBox.reference NKF_BoxModel.outer NJQ_Canonical.checkpoint decoded raw
 by_cases size : b.val.length = 192
 · rw [NJQ_CheckpointCut.model_closed b size]
   simp only [dif_pos size,NJQ_Canonical.mapOuter]
 · simp only [NJQ_Checkpoint.model,dif_neg size,NJQ_Canonical.mapOuter]
#print axioms source
end NMX_CheckpointValue
end
