import NMS_RequestModels
import NMS_R2N_Interpreted
set_option autoImplicit false
noncomputable section
namespace NMS_R2LaneModel
open Aeneas Aeneas.Std Result AdapterRw
/-- The exact CLOSED156 result on the native digest carrier, including every
noncanonical rejection, followed by the frozen adapter error conversion. -/
def result (digest : Array U32 8#usize) :
 core.result.Result U8 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 :=
 match NFY_NBN_OutputLane.result digest with
 | .Err _ => .Err .NonCanonicalDigest
 | .Ok lane => .Ok lane

theorem source (digest : Array U32 8#usize) :
 NMS_RequestModels.outputLane digest = ok (result digest) := by
 unfold NMS_RequestModels.outputLane
 rw [NFY_NBN_OutputLane.source,bind_tc_ok]
 unfold result
 cases NFY_NBN_OutputLane.result digest <;> rfl

theorem full (digest : Array U32 8#usize) :
 NMS_R2N_Interpreted.liftResult (NMS_RequestModels.outputLane digest) = RSL.Spec.pure (result digest) := by
 rw [source]
 rfl
#print axioms source
#print axioms full
end NMS_R2LaneModel
