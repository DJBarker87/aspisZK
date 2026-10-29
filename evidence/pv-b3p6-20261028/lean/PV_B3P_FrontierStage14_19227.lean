import PV_B3P_FrontierBase14227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier Result
set_option autoImplicit false
def suffix19_14 (fields : FF14) (out : alloc.vec.Vec U8) (values : FV14) : Result FS14 := do
  let a19 ←
    Array.index_usize values 19#usize
  let s19 ← lift (Array.to_slice a19)
  let (r19, out20) ← fields out s19
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
theorem factor19_14 (fields : FF14) (out : alloc.vec.Vec U8) (values : FV14) :
    suffix19_14 fields out values = frontier_step14 fields (suffix20_14 fields) 19#usize out values := by
  unfold suffix19_14 frontier_step14 suffix20_14
  rfl
#print axioms factor19_14
end PV_B3P_FrontierStages14227
