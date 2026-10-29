import PV_B3P_InclusiveCaller15227
import PV_B3P_NativePreweighted15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding12227 Result ControlFlow
set_option autoImplicit false

open PV_B3P_227
/-- The actual preweighted caller's bounded inclusive iteration is joined to
its owned loop. Macro and packed stores stay in their source order. -/
theorem preweighted_inclusive_caller15 {N : Usize}
    (start : Usize) (values : Array aspis_core.field.QM31 N)
    (last first : Usize) (limit : last.val < 24) (n : Nat)
    (packed : Array aspis_core.field.QM31 24#usize) (count : first.val+n=last.val+1) :
    inclusive_caller_loop15 (source_preweighted_macro_step12 start values) last first packed =
      reference_terminal.add_preweighted_loop packed start values last first := by
  rw [inclusive_caller_fold15 _ last first limit n packed count,preweighted_loop_binding12]
  have steps : source_preweighted_macro_step12 start values = preweighted_source_step12 start values := by
    funext state group
    exact preweighted_macro_step_binding12 start values state group
  rw [steps]
  exact (inclusive_loop_fold12 _ last first limit n packed count).symm
#print axioms preweighted_inclusive_caller15
end PV_B3P_Native15227
