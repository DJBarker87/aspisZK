import RPz7_S1SemanticCodeSampleBlockV1
import RPz7_S1SemanticFinishModelV1
import RPz7_S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)

def semanticValidated
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
  Code ((core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
    (r1_wire.SemanticTranscript H))
  := do
  let row ← r1_wire.ValidatedRecord.impl.row record1
  if row > 24#u8
  then pure (core.result.Result.Err r1_wire.Error.InvalidRow, self)
  else
    let s ← r1_wire.ValidatedRecord.impl.framed record1
    let (r, self1) ←
      sampleBlock aspis_coreDigest32Inst
        self row s
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let q ← sampler.qm31_sample val
      pure (core.result.Result.Ok q, self1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual
      pure (r1, self1)

#print axioms semanticValidated
end AspisR1PublicPreparation.S1SemanticCode
