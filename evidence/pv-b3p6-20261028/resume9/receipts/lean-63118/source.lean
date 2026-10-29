import PV_B3P_ReadBody901227
import PV_B3P_UsizeLoop9227
import PV_B3P_Ordered227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Ordered227
set_option autoImplicit false

def sum_step (high : Array aspis_core.field.QM31 64#usize)
    (sum : aspis_core.field.QM31) (i : Usize) : Result aspis_core.field.QM31 := do
  let value ← Array.index_usize high i
  aspis_core.field.QM31.add sum value

attribute [local irreducible] aspis_core.field.QM31.add Array.index_usize

theorem sum_body_binding (high : Array aspis_core.field.QM31 64#usize)
    (stop : Usize) (sum : aspis_core.field.QM31) (i : Usize) :
    reference_terminal.sum_interval227_loop.body high stop sum i =
      usize_body (sum_step high) stop (sum,i) := by
  rw [reference_terminal_sum_interval227_loop_body_read_binding9]
  simp only [reference_terminal_sum_interval227_loop_body_direct_read9,
    reference_terminal_sum_interval227_loop_body_read_context9,usize_body,sum_step,bind_assoc]

theorem sum_loop_binding (high : Array aspis_core.field.QM31 64#usize)
    (stop : Usize) (sum : aspis_core.field.QM31) (i : Usize) :
    reference_terminal.sum_interval227_loop high stop sum i =
      loop (usize_body (sum_step high) stop) (sum,i) := by
  unfold reference_terminal.sum_interval227_loop
  apply congrArg (fun body => loop body (sum,i))
  funext state
  exact sum_body_binding high stop state.1 state.2

theorem sum_interval_binding (high : Array aspis_core.field.QM31 64#usize)
    (stop i : Usize) (n : Nat) (sum : aspis_core.field.QM31)
    (h : i.val+n=stop.val) :
    reference_terminal.sum_interval227 high sum i stop =
      usize_plan (sum_step high) n i sum := by
  change reference_terminal.sum_interval227_loop high stop sum i = _
  rw [sum_loop_binding]
  exact usize_loop_plan (sum_step high) stop i n sum h

#print axioms sum_body_binding
#print axioms sum_loop_binding
#print axioms sum_interval_binding
end PV_B3P_Binding9227
