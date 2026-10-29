import PV_B3P_P227_14
import PV_B3P_InternalBinding12227
import PV_B3P_ValueCallerBridge12227
import PV_B3P_PatternBinding12227
import PV_B3P_Operations12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false
def actual_context12_0 (operation : Array aspis_core.field.QM31 16#usize → Result (Array aspis_core.field.QM31 16#usize))
  (state : Array aspis_core.field.QM31 16#usize)
  (constant1 : aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  let q ← Array.index_usize state 0#usize
  let q1 ← aspis_core.field.QM31.add q constant1
  let q2 ← reference_poseidon.pow5 q1
  let state1 ← Array.update state 0#usize q2
  operation state1
theorem actual_caller_binding12_0 
  (state : Array aspis_core.field.QM31 16#usize)
  (constant1 : aspis_core.field.QM31) :
    @reference_poseidon.internal_round state constant1 = @actual_context12_0 source_internal12 state constant1 :=
  congrArg (fun (operation : Array aspis_core.field.QM31 16#usize → Result (Array aspis_core.field.QM31 16#usize)) => @actual_context12_0 operation state constant1) (funext internal_linear_binding12)
#print axioms actual_caller_binding12_0
end PV_B3P_Binding12227
