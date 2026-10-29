import PV_B3P_DigitRead10227
import PV_B3P_ValueRead906227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.square aspis_core.field.QM31.sub Array.index_usize Array.update Usize.wrapping_add

theorem digit_single_stage10_06 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (selector : aspis_core.field.QM31)
    (range : DigitRange10) :
    value_direct_stage9_06 packed openings selectors (selector,range) = (do
      let next ← PV_B3P_Ordered227.fold (digit_single_step10 openings.xor12_z (some 20#usize)) [5#usize, 6#usize, 7#usize, 8#usize, 9#usize] range
      .ok (selector,next)) := by
  unfold value_direct_stage9_06 value_read_context9_06
  conv_rhs => simp only [PV_B3P_Ordered227.fold,digit_single_step10,digit_finish10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  all_goals rfl

theorem digit_source_stage_binding10_06 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (selector : aspis_core.field.QM31)
    (range : DigitRange10) :
    value_direct_stage9_06 packed openings selectors (selector,range) = (do
      let next ← PV_B3P_Ordered227.fold (digit_source_step10 openings.xor12_z (some 20#usize)) [5#usize, 6#usize, 7#usize, 8#usize, 9#usize] range
      .ok (selector,next)) := by
  rw [digit_fold_read_binding10]
  exact digit_single_stage10_06 packed openings selectors selector range
#print axioms digit_single_stage10_06
#print axioms digit_source_stage_binding10_06
end PV_B3P_Binding10227
