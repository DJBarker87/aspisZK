import NCO_ParserRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_LoopSteps

theorem inner_done (payload : Slice U8) (i j next : Usize)
    (terminal : 8 ≤ j.val) (increment : i + 1#usize = ok next) :
    NCO_ParserRef.validate_ref_loop0_loop0.body payload i j = ok (.done (next, 1#u32)) := by
  have h : ¬j < 8#usize := by scalar_tac
  simp only [NCO_ParserRef.validate_ref_loop0_loop0.body, h, ite_false, increment, bind_tc_ok]

theorem outer_done (payload : Slice U8) (i count : Usize)
    (division : Slice.len payload / 32#usize = ok count) (terminal : count.val ≤ i.val) :
    NCO_ParserRef.validate_ref_loop0.body payload i = ok (.done (i, some (.Ok ()))) := by
  have h : ¬i < count := by scalar_tac
  simp only [NCO_ParserRef.validate_ref_loop0.body, division, bind_tc_ok, h, ite_false]

#print axioms inner_done
#print axioms outer_done
#check loop_unfold
#check loop.unfold
end NCO_LoopSteps
