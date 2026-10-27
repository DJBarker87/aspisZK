import R1Z.PV_CB_ForestProducerRoot
import R1Z.PV_CB_ProducerMetadataCarrier
set_option autoImplicit false
namespace R1Z.PV_CB_ForestProducerContract
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem source (row start count : Usize) (tweak_right : Bool) (out : Tuple)
    (run : PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right = ok out) :
    (PV_CB_TupleProducerCarrier.tuple out).row = UScalar.cast .U16 row ∧ ∃ bank,
      PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.bank_for_row row = ok bank ∧
      PV_CB_CanonicalArrays.Valid (PV_CB_ProducerMetadataCarrier.FullLimb row bank)
        (PV_CB_TupleProducerCarrier.tuple out).limbs := by
  rw [PV_CB_ForestProducerRoot.legacy] at run
  obtain ⟨hr,bank,hb,vl⟩ := PV_CB_TupleProducerContract.source row start count tweak_right out run
  exact ⟨hr,bank,hb,PV_CB_ProducerMetadataCarrier.limbs row bank out.limbs vl⟩
#print axioms source
end R1Z.PV_CB_ForestProducerContract
