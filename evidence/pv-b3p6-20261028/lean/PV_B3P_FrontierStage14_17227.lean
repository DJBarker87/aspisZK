import PV_B3P_FrontierStage14_18227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier
set_option autoImplicit false
def suffix17_14 (fields : FF14) (out : alloc.vec.Vec U8) (values : FV14) : Result FS14 := do
  let a17 ←
    Array.index_usize values 17#usize
  let s17 ← lift (Array.to_slice a17)
  let (r17, out18) ← fields out s17
  let cf17 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r17
  match cf17 with
  |
    core.ops.control_flow.ControlFlow.Continue
    _ =>
    let a18 ←
      Array.index_usize values 18#usize
    let s18 ← lift (Array.to_slice a18)
    let (r18, out19) ← fields out18 s18
    let cf18 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r18
    match cf18 with
    |
      core.ops.control_flow.ControlFlow.Continue
      _ =>
      let a19 ←
        Array.index_usize values 19#usize
      let s19 ← lift (Array.to_slice a19)
      let (r19, out20) ← fields out19 s19
      let cf19 ←
        core.result.Result.Insts.CoreOpsTry.branch
          r19
      match cf19 with
      |
        core.ops.control_flow.ControlFlow.Continue
        _ =>
        ok (core.result.Result.Ok (), out20)
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r20 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame
            aspis_core.state_only_prefix.r0.Error)
            residual
        ok (r20, out20)
    | core.ops.control_flow.ControlFlow.Break
      residual =>
      let r19 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame
          aspis_core.state_only_prefix.r0.Error)
          residual
      ok (r19, out19)
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    let r18 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        aspis_core.state_only_prefix.r0.Error)
        residual
    ok (r18, out18)
theorem factor17_14 (fields : FF14) (out : alloc.vec.Vec U8) (values : FV14) :
    suffix17_14 fields out values = frontier_step14 fields (suffix18_14 fields) 17#usize out values := by
  unfold suffix17_14 frontier_step14 suffix18_14
  rfl
#print axioms factor17_14
end PV_B3P_FrontierStages14227
