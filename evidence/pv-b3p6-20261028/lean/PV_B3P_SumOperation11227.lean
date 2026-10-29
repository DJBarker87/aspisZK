import PV_B3P_SumLoopBinding9227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

abbrev SumOperation11 := Array aspis_core.field.QM31 64#usize → aspis_core.field.QM31 → Usize → Usize → Result aspis_core.field.QM31

def source_sum_interval11 : SumOperation11 := fun high initial start stop =>
  loop (usize_body (sum_step high) stop) (initial,start)

theorem sum_operation_binding11 : reference_terminal.sum_interval227 = source_sum_interval11 := by
  funext high initial start stop
  change reference_terminal.sum_interval227_loop high stop initial start = _
  exact sum_loop_binding high stop initial start

#print axioms sum_operation_binding11
end PV_B3P_Binding11227
