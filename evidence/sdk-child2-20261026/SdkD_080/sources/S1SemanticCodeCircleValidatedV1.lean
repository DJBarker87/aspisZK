import S1SemanticCodeSampleBlockV1
import S1SemanticFinishModelV1
import S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)

def circleValidated (B : FinishModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
  Code ((core.result.Result aspis_core.circle.SecureCirclePoint
    r1_wire.Error) × (r1_wire.SemanticTranscript H))
  := do
  let row ← r1_wire.ValidatedRecord.impl.row record1
  match row with
  | 25#uscalar =>
    let s ← r1_wire.ValidatedRecord.impl.framed record1
    let (r, self1) ←
      sampleBlock aspis_coreDigest32Inst
        self 25#u8 s
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let scp ← B.circle val FinishModel.CircleRow.First
      pure (core.result.Result.Ok scp, self1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.circle.SecureCirclePoint (core.convert.FromSame
          r1_wire.Error) residual
      pure (r1, self1)
  | 26#uscalar =>
    let s ← r1_wire.ValidatedRecord.impl.framed record1
    let (r, self1) ←
      sampleBlock aspis_coreDigest32Inst
        self 26#u8 s
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let scp ← B.circle val FinishModel.CircleRow.Second
      pure (core.result.Result.Ok scp, self1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.circle.SecureCirclePoint (core.convert.FromSame
          r1_wire.Error) residual
      pure (r1, self1)
  | _ => pure (core.result.Result.Err r1_wire.Error.InvalidRow, self)

#print axioms circleValidated
end AspisR1PublicPreparation.S1SemanticCode
