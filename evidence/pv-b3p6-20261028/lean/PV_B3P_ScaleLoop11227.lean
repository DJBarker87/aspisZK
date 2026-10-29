import PV_B3P_ScaleCompose11227
import PV_B3P_Indices3311227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
theorem scaling_stages_loop11 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    scaling_stages11 packed openings selectors state =
      loop (usize_body scale_frame11 33#usize) (state,0#usize) := by
  rw [loop_as_fold11 scale_frame11 33#usize 0#usize 33 state (Eq.refl _),indices11_33]
  exact scaling_stages_fold11 packed openings selectors state
#print axioms scaling_stages_loop11
end PV_B3P_Binding11227
