import PV_B3P_P227_14
import PV_B3P_InternalBinding12227
import PV_B3P_ValueCallerBridge12227
import PV_B3P_PatternBinding12227
import PV_B3P_Operations12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false
def actual_context12_2 (operation : reference_copy_terminal.Selectors → Result aspis_core.field.QM31)
  (openings : Array aspis_core.field.QM31 16#usize)
  (h1_z : aspis_core.field.QM31)
  (selectors : reference_copy_terminal.Selectors)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
  (append_index : Std.U64)
  (variant : reference_copy_terminal.PoolV1PairForestCompiledVariantV1) :
  Result reference_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1
  := do
  let patterns ← reference_copy_terminal.pattern_values openings lambda
  let a := Array.repeat 2#usize aspis_core.field.QM31.ZERO
  let a1 := Array.repeat 2#usize aspis_core.field.QM31.ZERO
  let a2 := Array.repeat 2#usize aspis_core.field.QM31.ZERO
  let a3 := Array.repeat 2#usize aspis_core.field.QM31.ZERO
  let (a4, a5, a6, a7) ←
    reference_copy_terminal.evaluate_with_selectors_loop selectors append_index
      variant patterns a a1 a2 a3 0#usize
  let active ← operation selectors
  let q ←
    reference_copy_terminal.copy_residual
      {
        producer_values := a4,
        producer_weights := a5,
        consumer_values := a6,
        consumer_weights := a7
      } h1_z chi
  let q1 ← aspis_core.field.QM31.mul active q
  ok { residual := q1, active }
theorem actual_caller_binding12_2 
  (openings : Array aspis_core.field.QM31 16#usize)
  (h1_z : aspis_core.field.QM31)
  (selectors : reference_copy_terminal.Selectors)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
  (append_index : Std.U64)
  (variant : reference_copy_terminal.PoolV1PairForestCompiledVariantV1) :
    @reference_copy_terminal.evaluate_with_selectors openings h1_z selectors lambda chi append_index variant = @actual_context12_2 source_active12 openings h1_z selectors lambda chi append_index variant :=
  congrArg (fun (operation : reference_copy_terminal.Selectors → Result aspis_core.field.QM31) => @actual_context12_2 operation openings h1_z selectors lambda chi append_index variant) active_operation12
#print axioms actual_caller_binding12_2
end PV_B3P_Binding12227
