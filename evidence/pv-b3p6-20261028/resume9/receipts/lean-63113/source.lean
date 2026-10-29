import PV_B3P_P227_09
import PV_B3P_ReadFunctions9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

/-- Exact emitted body context; only the immutable-read callee is abstracted. -/
def reference_terminal_sum_interval227_loop_body_read_context9 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (high : Array aspis_core.field.QM31 64#usize) (end1 : Std.Usize)
  (sum : aspis_core.field.QM31) (i : Std.Usize)  :
  Result (ControlFlow (aspis_core.field.QM31 × Std.Usize)
    aspis_core.field.QM31) :=  do
  if i < end1
  then
    let q ← source_read high i
    let sum1 ← aspis_core.field.QM31.add sum q
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (sum1, i1))
  else ok (done sum)

def reference_terminal_sum_interval227_loop_body_direct_read9 (high : Array aspis_core.field.QM31 64#usize) (end1 : Std.Usize)
  (sum : aspis_core.field.QM31) (i : Std.Usize)  :
  Result (ControlFlow (aspis_core.field.QM31 × Std.Usize)
    aspis_core.field.QM31) :=
  reference_terminal_sum_interval227_loop_body_read_context9 (fun values i => Array.index_usize values i) high end1 sum i

theorem reference_terminal_sum_interval227_loop_body_read_binding9 (high : Array aspis_core.field.QM31 64#usize) (end1 : Std.Usize)
  (sum : aspis_core.field.QM31) (i : Std.Usize)  :
    reference_terminal.sum_interval227_loop.body high end1 sum i = reference_terminal_sum_interval227_loop_body_direct_read9 high end1 sum i :=
  congrArg (fun source_read => reference_terminal_sum_interval227_loop_body_read_context9 source_read high end1 sum i) read_function_binding

#print axioms reference_terminal_sum_interval227_loop_body_read_binding9
end PV_B3P_Binding9227
