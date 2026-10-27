import R1Z.PV_CB_ForestProducerRoot
import R1Z.PV_CB_TupleProducerCarrier
set_option autoImplicit false
namespace R1Z.PV_CB_ForestProducerCarrier
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem produced (row start count : Usize) (tweak_right : Bool) (out : Tuple)
    (run : PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right = ok out) :
    PV_CB_CanonicalArrays.Valid PV_CB_ProducerLimb.OffsetValid (PV_CB_TupleProducerCarrier.tuple out).limbs :=
  PV_CB_TupleProducerCarrier.limbs_valid out.limbs
    (PV_CB_ForestProducerRoot.source row start count tweak_right out run)
#print axioms produced
end R1Z.PV_CB_ForestProducerCarrier
