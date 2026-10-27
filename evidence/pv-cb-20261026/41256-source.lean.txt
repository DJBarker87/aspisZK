import R1Z.PV_CB_TupleProducerRoot
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerSelectors
open Aeneas Aeneas.Std Result

/-- Explicit satisfiability witness only; never installed as the shipped range
    implementation. The producer postcondition is uniform over every selector. -/
def constant (run : Result Bool) : PV_CB_ShippedOp223Tuple.ExternalFuns where
  contains := fun _ _ _ _ _ => run

theorem inhabited : Nonempty PV_CB_ShippedOp223Tuple.ExternalFuns :=
  ⟨constant (ok false)⟩

theorem uniform (run : Result Bool) (row start count : Usize) (tweak_right : Bool) :
    PV_CB_PartialForward.Post PV_CB_TupleProducerRoot.ValidTuple
      (@PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells (constant run)
        row start count tweak_right) :=
  @PV_CB_TupleProducerRoot.source (constant run) row start count tweak_right
#print axioms inhabited
#print axioms uniform
end R1Z.PV_CB_TupleProducerSelectors
