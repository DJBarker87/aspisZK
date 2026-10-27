import R1Z.PV_CB_TupleProducerRootTotal
import R1Z.PV_CB_ForestProducerRoot
set_option autoImplicit false
namespace R1Z.PV_CB_ForestProducerTotal
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem source (row start count : Usize) (bound : count.val ≤ 16)
    (tweak_right : Bool) (bank : Bank)
    (selected : PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.bank_for_row row = ok bank) :
    ∃ out, PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right = ok out ∧
      PV_CB_TupleProducerRoot.ValidTuple out := by
  rw [PV_CB_ForestProducerRoot.legacy]
  exact PV_CB_TupleProducerRootTotal.source row start count bound tweak_right bank selected
#print axioms source
end R1Z.PV_CB_ForestProducerTotal
