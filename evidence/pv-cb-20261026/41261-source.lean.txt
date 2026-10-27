import R1Z.PV_CB_ForestProducerLoop
import R1Z.PV_CB_TupleProducerRoot
set_option autoImplicit false
namespace R1Z.PV_CB_ForestProducerRoot
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem legacy (row start count : Usize) (tweak_right : Bool) :
    PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right =
    PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells row start count tweak_right := by
  simp only [PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells,
    PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells,
    PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.bank_for_row,
    PV_CB_ForestProducerLoop.legacy,bind_assoc_eq,bind_tc_ok]

theorem source (row start count : Usize) (tweak_right : Bool) :
    PV_CB_PartialForward.Post PV_CB_TupleProducerRoot.ValidTuple
      (PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right) := by
  rw [legacy]
  exact PV_CB_TupleProducerRoot.source row start count tweak_right
#print axioms legacy
#print axioms source
end R1Z.PV_CB_ForestProducerRoot
