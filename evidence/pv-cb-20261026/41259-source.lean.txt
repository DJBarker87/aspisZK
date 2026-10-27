import R1Z.PV_CB_Op223ForestProducerFuns
import R1Z.PV_CB_TupleProducerBody
set_option autoImplicit false
namespace R1Z.PV_CB_ForestProducerBody
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]

/-- Equality of the two actual emitted loop bodies; range selection is outside
    the loop and neither body has an opaque arithmetic implementation. -/
theorem legacy (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (iter : PV_CB_ForwardRange.Range) (limbs : Array Limb 16#usize) :
    PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells_loop.body
      row start count tweak_right bank iter limbs =
    PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells_loop.body
      row start count tweak_right bank iter limbs := by
  rfl
#print axioms legacy
end R1Z.PV_CB_ForestProducerBody
