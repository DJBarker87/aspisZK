import PV_B3P_P227_14
import PV_B3P_EqualityBinding9227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false
def context12_equality_reference_terminal_terminal_parts (operation : Array aspis_core.field.QM31 10#usize → Array aspis_core.field.QM31 10#usize → Result aspis_core.field.QM31)
  (public1 : reference_terminal.SemanticPublic)
  (claims : Array aspis_core.field.QM31 84#usize)
  (point : Array aspis_core.field.QM31 10#usize)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
  (theta : aspis_core.field.QM31)
  (zerocheck_point : Array aspis_core.field.QM31 10#usize)
  (mu : aspis_core.field.QM31) :
  Result (core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 16#usize) × (Array aspis_core.field.QM31 10#usize)
    × aspis_core.field.QM31)
    reference_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  := do
  let r ←
    reference_terminal.composition_parts public1 claims point lambda chi theta
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (composition, c1, mask_only, g, h1_z, copy_active) := val
    let q ← operation zerocheck_point point
    let q1 ← aspis_core.field.QM31.mul q composition
    let q2 ← aspis_core.field.QM31.mul mu h1_z
    let q3 ← aspis_core.field.QM31.add q1 q2
    let q4 ← aspis_core.field.QM31.mul mu mu
    let q5 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE copy_active
    let q6 ← aspis_core.field.QM31.mul q5 h1_z
    let q7 ← aspis_core.field.QM31.mul q4 q6
    let original ← aspis_core.field.QM31.add q3 q7
    ok (core.result.Result.Ok (original, c1, mask_only, g))
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (aspis_core.field.QM31 × (Array aspis_core.field.QM31 16#usize) ×
      (Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
      (core.convert.FromSame
      reference_terminal.PoolV1PairForestSemanticTerminalErrorV1) residual
theorem caller12_equality_reference_terminal_terminal_parts 
  (public1 : reference_terminal.SemanticPublic)
  (claims : Array aspis_core.field.QM31 84#usize)
  (point : Array aspis_core.field.QM31 10#usize)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
  (theta : aspis_core.field.QM31)
  (zerocheck_point : Array aspis_core.field.QM31 10#usize)
  (mu : aspis_core.field.QM31) :
    @reference_terminal.terminal_parts public1 claims point lambda chi theta zerocheck_point mu = @context12_equality_reference_terminal_terminal_parts (PV_B3P_Binding9227.source_equality_value) public1 claims point lambda chi theta zerocheck_point mu :=
  congrArg (fun (operation : Array aspis_core.field.QM31 10#usize → Array aspis_core.field.QM31 10#usize → Result aspis_core.field.QM31) => @context12_equality_reference_terminal_terminal_parts @operation public1 claims point lambda chi theta zerocheck_point mu) (funext fun left => funext fun right => (PV_B3P_Binding9227.equality_body_binding left right).symm)
#print axioms caller12_equality_reference_terminal_terminal_parts
end PV_B3P_Binding12227
