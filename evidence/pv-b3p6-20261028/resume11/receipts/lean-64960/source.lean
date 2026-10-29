import PV_B3P_ScaleStage1108227
import PV_B3P_ScaleStage1109227
import PV_B3P_ScaleStage1110227
import PV_B3P_ScaleStage1111227
import PV_B3P_ScaleStage1112227
import PV_B3P_ScaleStage1113227
import PV_B3P_ScalePartition11227
import PV_B3P_NineUnroll9227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
attribute [local irreducible] scale_frame11 value_direct_stage9_08 value_direct_stage9_09 value_direct_stage9_10 value_direct_stage9_11 value_direct_stage9_12 value_direct_stage9_13
def scaling_stages11 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let s8 ← value_direct_stage9_08 packed openings selectors state
  let s9 ← value_direct_stage9_09 packed openings selectors s8
  let s10 ← value_direct_stage9_10 packed openings selectors s9
  let s11 ← value_direct_stage9_11 packed openings selectors s10
  let s12 ← value_direct_stage9_12 packed openings selectors s11
  value_direct_stage9_13 packed openings selectors s12
theorem scaling_stages_fold11 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    scaling_stages11 packed openings selectors state =
      PV_B3P_Ordered227.fold scale_frame11 [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize, 16#usize, 17#usize, 18#usize, 19#usize, 20#usize, 21#usize, 22#usize, 23#usize, 24#usize, 25#usize, 26#usize, 27#usize, 28#usize, 29#usize, 30#usize, 31#usize, 32#usize] state := by
  unfold scaling_stages11
  simp only [scale_stage11_08,scale_stage11_09,scale_stage11_10,scale_stage11_11,scale_stage11_12,scale_stage11_13]
  have h := PV_B3P_Ordered227.flatten scale_frame11 [[0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize], [6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize], [12#usize, 13#usize, 14#usize, 15#usize, 16#usize, 17#usize], [18#usize, 19#usize, 20#usize, 21#usize, 22#usize, 23#usize], [24#usize, 25#usize, 26#usize, 27#usize, 28#usize, 29#usize], [30#usize, 31#usize, 32#usize]] state
  rw [scale_partition11] at h
  simpa only [PV_B3P_Ordered227.ranges,bind_tc_ok,PV_B3P_Binding9227.result_right] using h
#print axioms scaling_stages_fold11
end PV_B3P_Binding11227
