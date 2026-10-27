import R1Z.PV_CB_TupleProducerStep
import R1Z.PV_CB_ForwardLoop
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerBody
open Aeneas Aeneas.Std Result ControlFlow PV_CB_TupleProducerOffset
abbrev body := PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells_loop.body

theorem source (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (iter : PV_CB_ForwardRange.Range) (limbs : Array Limb 16#usize) :
    body row start count tweak_right bank iter limbs =
    PV_CB_ForwardLoop.body (PV_CB_TupleProducerStep.step row start count tweak_right bank) iter limbs := by
  rcases iter with ⟨i,stop⟩
  by_cases more : i < stop
  · have hn := PV_CB_ForwardRange.next_step i stop more
    simp only [PV_CB_ForwardRange.next,PV_CB_ForwardRange.between] at hn
    simp only [body,PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells_loop.body,
      PV_CB_ForwardLoop.body,PV_CB_TupleProducerStep.step,offset,
      PV_CB_ForwardRange.next,PV_CB_ForwardRange.between,hn,more,if_true,
      lift,bind_tc_ok,bind_assoc_eq]
    first | rfl | rw [if_pos more]
  · have notmore : ¬i < stop := more
    have back : stop.val ≤ i.val := by
      change ¬i.val < stop.val at more
      omega
    have hn := PV_CB_ForwardRange.next_done i stop back
    simp only [PV_CB_ForwardRange.next,PV_CB_ForwardRange.between] at hn
    simp only [body,PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells_loop.body,
      PV_CB_ForwardLoop.body,PV_CB_ForwardRange.next,PV_CB_ForwardRange.between,
      hn,notmore,if_false,bind_tc_ok]
    first | rfl | rw [if_neg notmore]
#print axioms source
end R1Z.PV_CB_TupleProducerBody
