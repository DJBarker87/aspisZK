import NEM_PaymentReached
import NED_SubtreeComposition
set_option autoImplicit false
noncomputable section
namespace NEM_LaneReached
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult

def lane (d : Array U32 8#usize) :=
  pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 d

theorem lane_instance (d : Array U32 8#usize) :
    lane d = NBN_FirstByteDependency.lane NED_ValidatorTrace.enc d :=
  (NED_SubtreeComposition.output_lane d).symm

theorem lane_reached (late : NEE_ValidatorMutation.Late) (s : Statement)
    (d : Array U32 8#usize)
    (_reached : NED_ValidatorTrace.Call.lane d ∈
      (NEE_ValidatorOracle.run NEM_PaymentReached.pay lane late s).2) :
    lane d = NBN_FirstByteDependency.lane NED_ValidatorTrace.enc d := lane_instance d

#print axioms lane_instance
#print axioms lane_reached
end NEM_LaneReached
