import R1Z.PV_CB_ForestProducerCarrier
import R1Z.PV_CB_ProducerLocalSelected
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ForestProducedValues
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes] [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem canonical (ops : ExternalFuns) (row start count : Usize) (tweak_right : Bool)
    (out : PV_CB_TupleProducerOffset.Tuple)
    (produced : PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right = ok out)
    (trace : Trace)
    (reads : PV_CB_CanonicalArrays.Valid (PV_CB_ProducerLocalLimb.Reads trace)
      (PV_CB_TupleProducerCarrier.tuple out).limbs)
    (values : Array U32 16#usize)
    (run : @host_semantic.copy_tuple_values _ (PV_CurrentScaleInstall.selected ops)
      trace (PV_CB_TupleProducerCarrier.tuple out) = ok (.Ok values)) :
    PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid values :=
  PV_CB_ProducerLocalSelected.tuple ops trace _ reads
    (PV_CB_ForestProducerCarrier.produced row start count tweak_right out produced) values run
#print axioms canonical
end R1Z.PV_CB_ForestProducedValues
