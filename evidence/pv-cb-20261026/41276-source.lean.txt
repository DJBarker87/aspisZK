import R1Z.PV_CB_TupleProducerRoot
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerRow
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem source (row start count : Usize) (tweak_right : Bool) :
    PV_CB_PartialForward.Post (fun out : Tuple => out.row = UScalar.cast .U16 row)
      (PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells row start count tweak_right) := by
  unfold PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells
  apply PV_CB_PartialForward.bind
  intro bank hb
  apply PV_CB_PartialForward.bind
  intro limbs hl
  simp only [lift,bind_tc_ok]
  intro out h
  cases h
  rfl
#print axioms source
end R1Z.PV_CB_TupleProducerRow
