import S1SemanticCodeRoundStepV1
import S1SemanticFinishModelV1
import S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)

def rounds (B : RoundModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
  Code (core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 10#usize) × (r1_wire.SemanticTranscript H))
    r1_wire.Error)
  := do
  let r ← r1_wire.Prefix.validated_record prefix1 14#u8
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let r1 ← B.decode 1#usize vr 0#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let running ← Array.index_usize val 0#usize
      let alpha := Array.repeat 10#usize aspis_core.field.QM31.ZERO
      let r2 ←
        roundStep B aspis_coreDigest32Inst prefix1 transcript
          alpha running 0#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let (running1, alpha1, transcript1) := val1
        let r3 ←
          roundStep B aspis_coreDigest32Inst prefix1 transcript1
            alpha1 running1 1#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let (running2, alpha2, transcript2) := val2
          let r4 ←
            roundStep B aspis_coreDigest32Inst prefix1
              transcript2 alpha2 running2 2#usize
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let (running3, alpha3, transcript3) := val3
            let r5 ←
              roundStep B aspis_coreDigest32Inst prefix1
                transcript3 alpha3 running3 3#usize
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let (running4, alpha4, transcript4) := val4
              let r6 ←
                roundStep B aspis_coreDigest32Inst prefix1
                  transcript4 alpha4 running4 4#usize
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                let (running5, alpha5, transcript5) := val5
                let r7 ←
                  roundStep B aspis_coreDigest32Inst prefix1
                    transcript5 alpha5 running5 5#usize
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val6 =>
                  let (running6, alpha6, transcript6) := val6
                  let r8 ←
                    roundStep B aspis_coreDigest32Inst prefix1
                      transcript6 alpha6 running6 6#usize
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue val7 =>
                    let (running7, alpha7, transcript7) := val7
                    let r9 ←
                      roundStep B aspis_coreDigest32Inst prefix1
                        transcript7 alpha7 running7 7#usize
                    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val8 =>
                      let (running8, alpha8, transcript8) := val8
                      let r10 ←
                        roundStep B aspis_coreDigest32Inst
                          prefix1 transcript8 alpha8 running8 8#usize
                      let cf10 ←
                        core.result.Result.Insts.CoreOpsTry.branch r10
                      match cf10 with
                      | core.ops.control_flow.ControlFlow.Continue val9 =>
                        let (running9, alpha9, transcript9) := val9
                        let r11 ←
                          roundStep B aspis_coreDigest32Inst
                            prefix1 transcript9 alpha9 running9 9#usize
                        let cf11 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf11 with
                        | core.ops.control_flow.ControlFlow.Continue val10 =>
                          pure (core.result.Result.Ok val10)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (aspis_core.field.QM31 × (Array
                            aspis_core.field.QM31 10#usize) ×
                            (r1_wire.SemanticTranscript H))
                            (core.convert.FromSame r1_wire.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (aspis_core.field.QM31 × (Array
                          aspis_core.field.QM31 10#usize) ×
                          (r1_wire.SemanticTranscript H))
                          (core.convert.FromSame r1_wire.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                        10#usize) × (r1_wire.SemanticTranscript H))
                        (core.convert.FromSame r1_wire.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                      10#usize) × (r1_wire.SemanticTranscript H))
                      (core.convert.FromSame r1_wire.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                    10#usize) × (r1_wire.SemanticTranscript H))
                    (core.convert.FromSame r1_wire.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                  10#usize) × (r1_wire.SemanticTranscript H))
                  (core.convert.FromSame r1_wire.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                10#usize) × (r1_wire.SemanticTranscript H))
                (core.convert.FromSame r1_wire.Error) residual
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
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
      (r1_wire.SemanticTranscript H)) (core.convert.FromSame r1_wire.Error)
      residual

#print axioms rounds
end AspisR1PublicPreparation.S1SemanticCode
