import PV_B3P_RangeFold13227
import PV_B3P_LinkDefinitions13227
import PV_B3P_SumOperation11227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 Result
set_option autoImplicit false

def source_sum_ranges13 (high : Array aspis_core.field.QM31 64#usize) :
    List (Usize × Usize) → aspis_core.field.QM31 → Result aspis_core.field.QM31
  | [], sum => .ok sum
  | (start,finish)::ranges, sum => do
      let next ← range_loop13 (sum_step high) start finish sum
      source_sum_ranges13 high ranges next

theorem sum_ranges_binding13 (high : Array aspis_core.field.QM31 64#usize)
    (ranges : List (Usize × Usize)) (sum : aspis_core.field.QM31) :
    source_sum_ranges13 high ranges sum = PV_B3P_Links13227.sum_ranges_reference13 high ranges sum := by
  induction ranges generalizing sum with
  | nil => rfl
  | cons range ranges ih =>
    rcases range with ⟨start,finish⟩
    simp only [source_sum_ranges13,PV_B3P_Links13227.sum_ranges_reference13,range_loop_binding13]
    have interval := congrFun (congrFun (congrFun (congrFun sum_operation_binding11 high) sum) start) finish
    unfold source_sum_interval11 at interval
    rw [←interval]
    apply congrArg (Aeneas.Std.bind _)
    funext next
    exact ih next

def source_sum_high13 (selectors : reference_copy_terminal.Selectors) (ranges : List (Usize × Usize)) :=
  source_sum_ranges13 selectors.high ranges aspis_core.field.QM31.ZERO

theorem sum_high_link13 : PV_B3P_Links13227.PV_B3P_Link_terminal_sum_high source_sum_high13 :=
  fun selectors ranges => sum_ranges_binding13 selectors.high ranges aspis_core.field.QM31.ZERO
#print axioms sum_ranges_binding13
#print axioms sum_high_link13
end PV_B3P_Binding13227
