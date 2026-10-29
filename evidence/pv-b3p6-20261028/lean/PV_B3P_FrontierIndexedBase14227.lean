import PV_B3P_FrontierStage14_00227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
def indexed14 (fields : FF14) : List Usize → alloc.vec.Vec U8 → FV14 → Result FS14
  | [],out,_ => .ok (.Ok (),out)
  | index::rest,out,values => frontier_step14 fields (fun out values => indexed14 fields rest out values) index out values

theorem suffix20_binding14 (fields : FF14) : suffix20_14 fields = indexed14 fields [] := rfl

theorem raw_frontier_binding14 (fields : FF14) : frontier fields = suffix0_14 fields := by
  funext out values
  unfold frontier suffix0_14
  rfl
#print axioms suffix20_binding14
#print axioms raw_frontier_binding14
#print alloc.vec.Vec
end PV_B3P_FrontierStages14227
