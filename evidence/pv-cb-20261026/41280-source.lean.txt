import R1Z.PV_CB_TupleProducerMetadataRoot
import R1Z.PV_CB_TupleProducerRow
import R1Z.PV_CB_ForestProducerRoot
set_option autoImplicit false
namespace R1Z.PV_CB_ForestProducerMetadata
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem row (row start count : Usize) (tweak_right : Bool) :
    PV_CB_PartialForward.Post (fun out : Tuple => out.row = UScalar.cast .U16 row)
      (PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right) := by
  rw [PV_CB_ForestProducerRoot.legacy]
  exact PV_CB_TupleProducerRow.source row start count tweak_right

theorem source (row start count : Usize) (tweak_right : Bool) :
    PV_CB_PartialForward.Post (fun out : Tuple => ∃ bank,
      PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.bank_for_row row = ok bank ∧
      PV_CB_TupleProducerMetadata.Valid row bank out.limbs)
      (PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right) := by
  rw [PV_CB_ForestProducerRoot.legacy]
  exact PV_CB_TupleProducerMetadataRoot.source row start count tweak_right
#print axioms row
#print axioms source
end R1Z.PV_CB_ForestProducerMetadata
