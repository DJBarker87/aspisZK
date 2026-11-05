import NHT_EmittedCommon
set_option autoImplicit false
noncomputable section
namespace NHT_EmittedAuth
open Aeneas Aeneas.Std Result VTop_Stages
def tx2_authenticated (ops : VTop_Stages.Ops)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result Unit verifier.Error)
  := do
  let r ← ops.op3 proof
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    ops.op13 obs AdapterRw.aspis_r1_cost_probe.verifier.Phase.Parsed
    NHT_EmittedCommon.tx2_common ops aspis_coredigestDigest32Inst public_bytes
      proof checkpoint hash obs
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual

end NHT_EmittedAuth
