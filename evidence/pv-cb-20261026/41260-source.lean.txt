import R1Z.PV_CB_ForestProducerBody
import R1Z.PV_CB_TupleProducerLoop
set_option autoImplicit false
namespace R1Z.PV_CB_ForestProducerLoop
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem legacy (iter : PV_CB_ForwardRange.Range) (row start count : Usize)
    (tweak_right : Bool) (bank : Bank) (limbs : Array Limb 16#usize) :
    PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells_loop
      iter row start count tweak_right bank limbs =
    PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells_loop
      iter row start count tweak_right bank limbs := by
  simp only [PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells_loop,
    PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells_loop,PV_CB_ForestProducerBody.legacy]
#print axioms legacy
end R1Z.PV_CB_ForestProducerLoop
