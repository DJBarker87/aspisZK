import R1Z.PV_CB_TupleProducerTotal
import R1Z.PV_CB_TupleProducerRoot
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerRootTotal
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
variable [PV_CB_ShippedOp223Tuple.ExternalFuns]

/-- Totality is conditional only on the actual selector returning a bank.
    No selector output is asserted on behalf of shipped code. -/
theorem source (row start count : Usize) (bound : count.val ≤ 16)
    (tweak_right : Bool) (bank : Bank)
    (selected : PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.bank_for_row row = ok bank) :
    ∃ out, PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells row start count tweak_right = ok out ∧
      PV_CB_TupleProducerRoot.ValidTuple out := by
  obtain ⟨limbs,hl,vl⟩ := PV_CB_TupleProducerTotal.source row start count bound tweak_right bank _ initial
  refine ⟨{row := UScalar.cast .U16 row,limbs := limbs},?_,vl⟩
  simp only [PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells,selected,bind_tc_ok,
    PV_CB_ForwardRange.between] at hl ⊢
  simp only [hl,lift,bind_tc_ok]
#print axioms source
end R1Z.PV_CB_TupleProducerRootTotal
