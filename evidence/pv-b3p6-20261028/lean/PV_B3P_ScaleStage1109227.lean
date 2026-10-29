import PV_B3P_ScaleFrame11227
import PV_B3P_ValueRead909227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.mul
theorem scale_stage11_09 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_direct_stage9_09 packed openings selectors state =
      PV_B3P_Ordered227.fold scale_frame11 [6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize] state := by
  rcases state with ⟨selector,range⟩
  rw [scale_frame_fold11]
  unfold value_direct_stage9_09 value_read_context9_09
  conv_rhs => simp only [PV_B3P_Ordered227.fold,scale_cell11,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms scale_stage11_09
end PV_B3P_Binding11227
