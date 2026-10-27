import R1Z.PV_CB_TupleProducerInvariant
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerRoot
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]
def ValidTuple (tuple : Tuple) : Prop := Valid tuple.limbs

/-- Actual private Rust producer: all successful outputs have canonical
    offsets, uniformly over every range-selector callback. No count bound,
    chosen callback result, registry output or compressor outcome is assumed. -/
theorem source (row start count : Usize) (tweak_right : Bool) :
    PV_CB_PartialForward.Post ValidTuple
      (PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells row start count tweak_right) := by
  unfold PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells
  apply PV_CB_PartialForward.bind
  intro bank hb
  apply PV_CB_PartialForward.bind
  intro limbs hl
  have valid := PV_CB_TupleProducerInvariant.source row start count tweak_right bank _ initial limbs hl
  simp only [lift,bind_tc_ok]
  intro out h
  cases h
  exact valid
#print axioms source
end R1Z.PV_CB_TupleProducerRoot
