import PV_B3P_DigitRead10227
import PV_B3P_ValueRead901227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.square aspis_core.field.QM31.sub Array.index_usize Array.update Usize.wrapping_add

theorem digit_single_stage10_01 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (selector : aspis_core.field.QM31)
    (range : DigitRange10) :
    value_direct_stage9_01 packed openings selectors (selector,range) = (do
      let next ← PV_B3P_Ordered227.fold (digit_single_step10 openings.z none) [0#usize, 1#usize, 2#usize, 3#usize, 4#usize] range
      .ok (selector,next)) := by
  unfold value_direct_stage9_01 value_read_context9_01
  conv_rhs => simp only [PV_B3P_Ordered227.fold,digit_single_step10,digit_finish10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  all_goals rfl

theorem digit_source_stage_binding10_01 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (selector : aspis_core.field.QM31)
    (range : DigitRange10) :
    value_direct_stage9_01 packed openings selectors (selector,range) = (do
      let next ← PV_B3P_Ordered227.fold (digit_source_step10 openings.z none) [0#usize, 1#usize, 2#usize, 3#usize, 4#usize] range
      .ok (selector,next)) := by
  rw [digit_fold_read_binding10]
  exact digit_single_stage10_01 packed openings selectors selector range
#print axioms digit_single_stage10_01
#print axioms digit_source_stage_binding10_01
end PV_B3P_Binding10227
