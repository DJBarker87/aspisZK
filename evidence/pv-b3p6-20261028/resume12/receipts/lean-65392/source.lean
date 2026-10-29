import PV_B3P_P227_14
import PV_B3P_InternalBinding12227
import PV_B3P_ValueCallerBridge12227
import PV_B3P_PatternBinding12227
import PV_B3P_Operations12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false
def actual_context12_1 (operation : Array aspis_core.field.QM31 16#usize → aspis_core.field.QM31 → Result (Array aspis_core.field.QM31 14#usize))
  (openings : Array aspis_core.field.QM31 16#usize)
  (lambda : aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 14#usize)
  := do
  operation openings lambda
theorem actual_caller_binding12_1 
  (openings : Array aspis_core.field.QM31 16#usize)
  (lambda : aspis_core.field.QM31) :
    @reference_copy_terminal.pattern_values openings lambda = @actual_context12_1 source_pattern_values12 openings lambda :=
  congrArg (fun (operation : Array aspis_core.field.QM31 16#usize → aspis_core.field.QM31 → Result (Array aspis_core.field.QM31 14#usize)) => @actual_context12_1 operation openings lambda) (funext fun openings => funext fun lambda => pattern_values_literal_binding12 openings lambda)
#print axioms actual_caller_binding12_1
end PV_B3P_Binding12227
