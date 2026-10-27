import R1Z.PV_CB_TupleProducerBody
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerLoop
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset
abbrev loop := PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells_loop

theorem source (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (iter : PV_CB_ForwardRange.Range) (limbs : Array Limb 16#usize) :
    loop iter row start count tweak_right bank limbs =
      PV_CB_ForwardLoop.run (PV_CB_TupleProducerStep.step row start count tweak_right bank)
        iter.start iter.end limbs := by
  rcases iter with ⟨i,stop⟩
  simp only [loop,PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells_loop,
    PV_CB_TupleProducerBody.source,PV_CB_ForwardLoop.run,PV_CB_ForwardRange.between]

theorem finite (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (fuel : Nat) (i stop : Usize) (limbs : Array Limb 16#usize)
    (rank : i.val + fuel = stop.val) :
    loop (PV_CB_ForwardRange.between i stop) row start count tweak_right bank limbs =
      PV_CB_ForwardLoop.finite (PV_CB_TupleProducerStep.step row start count tweak_right bank) fuel i limbs := by
  rw [source]
  exact PV_CB_ForwardLoop.source _ fuel i stop limbs rank
#print axioms source
#print axioms finite
end R1Z.PV_CB_TupleProducerLoop
