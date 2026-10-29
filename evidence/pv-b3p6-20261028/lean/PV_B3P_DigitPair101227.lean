import PV_B3P_DigitLoop10227
import PV_B3P_DigitStage1003227
import PV_B3P_DigitStage1004227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] digit_source_step10 value_direct_stage9_03 value_direct_stage9_04

theorem digit_pair_loop_binding10_1
    (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (selector : aspis_core.field.QM31)
    (range : DigitRange10) :
    (do let first ← value_direct_stage9_03 packed openings selectors (selector,range)
        value_direct_stage9_04 packed openings selectors (selector,first.2)) = (do
      let next ← loop (usize_body (digit_source_step10 openings.succ_z (some 10#usize)) 10#usize) (range,0#usize)
      .ok (selector,next)) := by
  rw [digit_loop_ten10,digit_source_stage_binding10_03]
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  conv_lhs => arg 2; intro next; rw [digit_source_stage_binding10_04]
  have partition := PV_B3P_Ordered227.append (digit_source_step10 openings.succ_z (some 10#usize))
    [0#usize,1#usize,2#usize,3#usize,4#usize] [5#usize,6#usize,7#usize,8#usize,9#usize] range
  have lifted := congrArg (fun result => result >>= (fun next => Result.ok (selector,next))) partition
  exact (PV_B3P_Ordered227.bind_assoc
    (PV_B3P_Ordered227.fold (digit_source_step10 openings.succ_z (some 10#usize)) [0#usize,1#usize,2#usize,3#usize,4#usize] range)
    (PV_B3P_Ordered227.fold (digit_source_step10 openings.succ_z (some 10#usize)) [5#usize,6#usize,7#usize,8#usize,9#usize])
    (fun next => Result.ok (selector,next))).symm.trans lifted.symm
#print axioms digit_pair_loop_binding10_1
end PV_B3P_Binding10227
