import PV_B3P_SumHighLink13227
import PV_B3P_TransitionLoan14227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

open PV_B3P_Loans14227
/-- Slice order and the complete ordered list of range endpoints are retained.
Every source range is cloned by value; neither shared loan is changed. -/
def native_sum_high15 (selectors : Shared14 reference_copy_terminal.Selectors)
    (ranges : Shared14 (List (Usize × Usize))) : Result aspis_core.field.QM31 :=
  source_sum_ranges13 selectors.value.high ranges.value aspis_core.field.QM31.ZERO

theorem native_sum_high_binding15 (selectors : Shared14 reference_copy_terminal.Selectors)
    (ranges : Shared14 (List (Usize × Usize))) :
    native_sum_high15 selectors ranges =
      PV_B3P_Links13227.sum_ranges_reference13 selectors.value.high ranges.value aspis_core.field.QM31.ZERO :=
  sum_ranges_binding13 selectors.value.high ranges.value aspis_core.field.QM31.ZERO
#print axioms native_sum_high_binding15
end PV_B3P_Native15227
