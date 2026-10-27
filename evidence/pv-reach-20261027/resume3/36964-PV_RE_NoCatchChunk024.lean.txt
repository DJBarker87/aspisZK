import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix048
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.EncodingDomain.new`.
Recursive calls remain the original extracted calls. -/
def continueAfter  (out : Payload (host_commitment.domain_points)) : Result (core.result.Result host_commitment.EncodingDomain
    aspis_core.r0.Error) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r1, levels) ←
      alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new (alloc.vec.Vec
        aspis_core.field.M31)) 9#usize
    let r2 ←
      core.result.Result.map_err
        host_commitment.EncodingDomain.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s := alloc.vec.Vec.deref val
      let r3 ← host_commitment.domain_first_level s
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let levels1 ← alloc.vec.Vec.push levels val1
        let r4 ← host_commitment.domain_append_levels levels1 0#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ok (core.result.Result.Ok { xy := val, levels := val2 })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            host_commitment.EncodingDomain (core.convert.FromSame
            aspis_core.r0.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          host_commitment.EncodingDomain (core.convert.FromSame
          aspis_core.r0.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        host_commitment.EncodingDomain (core.convert.FromSame
        aspis_core.r0.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      host_commitment.EncodingDomain (core.convert.FromSame
      aspis_core.r0.Error) residual


end R1Z.PV_RE_NoCatchSuffix048
pv_no_catch_binds ProverRwFull.host_commitment.EncodingDomain.new
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix048.continueAfter
