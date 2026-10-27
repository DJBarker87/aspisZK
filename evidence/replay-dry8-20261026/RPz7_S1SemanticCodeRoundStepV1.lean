import RPz7_S1SemanticCodeSemanticValidatedV1
import RPz7_S1SemanticFinishModelV1
import RPz7_S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)

def roundStep (B : RoundModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
  (alpha : Array aspis_core.field.QM31 10#usize)
  (running : aspis_core.field.QM31) (round : Std.Usize) :
  Code (core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 10#usize) × (r1_wire.SemanticTranscript H))
    r1_wire.Error)
  := do
  let i ← lift (UScalar.cast .U8 round)
  let row ← 15#u8 + i
  let r ← r1_wire.Prefix.validated_record prefix1 row
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let r1 ← B.decode 28#usize vr 0#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let boundary ← B.boundary val
      let b ←
        core.cmp.PartialEq.ne.trait_default
          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 boundary running
      if b
      then pure (core.result.Result.Err (r1_wire.Error.Boundary round))
      else
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue vr1 =>
          let (r2, transcript1) ←
            semanticValidated
              aspis_coreDigest32Inst transcript vr1
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            let alpha1 ← Array.update alpha round val1
            let value ← B.value val alpha1 round
            pure (core.result.Result.Ok (value, alpha1, transcript1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize)
              × (r1_wire.SemanticTranscript H)) (core.convert.FromSame
              r1_wire.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
            (r1_wire.SemanticTranscript H)) (core.convert.FromSame
            r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
        (r1_wire.SemanticTranscript H)) (core.convert.FromSame r1_wire.Error)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
      (r1_wire.SemanticTranscript H)) (core.convert.FromSame r1_wire.Error)
      residual

#print axioms roundStep
end AspisR1PublicPreparation.S1SemanticCode
