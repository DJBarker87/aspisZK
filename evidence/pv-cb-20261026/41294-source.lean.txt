import R1Z.PV_CB_TupleProducerMetadataRoot
import R1Z.PV_CB_TupleProducerRow
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerContract
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem source (row start count : Usize) (tweak_right : Bool) (out : Tuple)
    (run : PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells row start count tweak_right = ok out) :
    out.row = UScalar.cast .U16 row ∧ ∃ bank,
      PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.bank_for_row row = ok bank ∧
      PV_CB_TupleProducerMetadata.Valid row bank out.limbs :=
  ⟨PV_CB_TupleProducerRow.source row start count tweak_right out run,
   PV_CB_TupleProducerMetadataRoot.source row start count tweak_right out run⟩
#print axioms source
end R1Z.PV_CB_TupleProducerContract
