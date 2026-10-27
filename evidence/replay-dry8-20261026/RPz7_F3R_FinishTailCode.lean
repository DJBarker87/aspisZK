import RPz7_S1SemanticCodeFinishV1
set_option autoImplicit false
namespace AspisR1.F3R_FinishTailCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode S1SemanticCode

def code (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (challenges : r1_wire.Challenges)
    (alpha : Array aspis_core.field.QM31 10#usize)
    (val1 : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (val3 : Array aspis_core.field.QM31 29#usize)
    (state_before_z0 : Array U8 32#usize)
    (val4 : aspis_core.circle.SecureCirclePoint)
    (transcript2 : r1_wire.SemanticTranscript H) : Code (core.result.Result (r1_semantic.Verified H) r1_wire.Error) := do
  let r7 ← r1_wire.Prefix.validated_record prefix1 26#u8
  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
  match cf7 with
  | core.ops.control_flow.ControlFlow.Continue vr2 =>
    let r8 ←
      R.decode 29#usize vr2 0#usize
    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
    match cf8 with
    | core.ops.control_flow.ControlFlow.Continue val5 =>
      let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r7
      match cf9 with
      | core.ops.control_flow.ControlFlow.Continue vr3 =>
        let (r9, transcript3) ←
          circleValidated B
            aspis_coreDigest32Inst transcript2 vr3
        let cf10 ←
          core.result.Result.Insts.CoreOpsTry.branch r9
        match cf10 with
        | core.ops.control_flow.ControlFlow.Continue val6 =>
          VerifyPrefix.mark none 5#u8
          let b1 ←
            FinishModel.pointEq
              val4 val6
          if b1
          then
            pure (core.result.Result.Err
              r1_wire.Error.EqualCirclePoints)
          else
            let r10 ← FinishModel.payload prefix1 2#u8
            let cf11 ←
              core.result.Result.Insts.CoreOpsTry.branch r10
            match cf11 with
            | core.ops.control_flow.ControlFlow.Continue val7
              =>
              let r11 ←
                core.array.TryFromArrayCopySlice.try_from
                  32#usize core.marker.CopyU8 val7
              let a3 ←
                B.unwrapRoot r11
              pure (core.result.Result.Ok
                {
                  roots :=
                    (Array.make 2#usize [
                      prefix1.c1_root, a3
                      ]),
                  challenges,
                  alpha,
                  claims := val1,
                  extra := val3,
                  before_z1 := val5,
                  state_before_z0,
                  z := (Array.make 2#usize [ val4, val6 ]),
                  transcript := transcript3
                })
            | core.ops.control_flow.ControlFlow.Break residual
              =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (r1_semantic.Verified H) (core.convert.FromSame
                r1_wire.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (r1_semantic.Verified H) (core.convert.FromSame
            r1_wire.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame
          r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame
        r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

end AspisR1.F3R_FinishTailCode
