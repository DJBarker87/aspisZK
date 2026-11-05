import NHG_Begin5
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode (Code)
namespace AspisR1.NHG_BeginPackets
def begin
  {H : Type} (packet : aspis_core.Digest32 H → r1_wire.SemanticTranscript H → r1_wire.ValidatedRecord → Code ((core.result.Result aspis_core.field.QM31 r1_wire.Error) × r1_wire.SemanticTranscript H)) (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
  Code ((core.result.Result r1_wire.Challenges r1_wire.Error) ×
    (r1_wire.SemanticTranscript H))
  := do
  let r ← r1_wire.Prefix.validated_record prefix1 0#u8
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let (r1, transcript1) ←
      packet aspis_coreDigest32Inst
        transcript vr
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r2 ← r1_wire.Prefix.validated_record prefix1 1#u8
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue vr1 =>
        let (r3, transcript2) ←
          packet aspis_coreDigest32Inst
            transcript1 vr1
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let r4 ← r1_wire.Prefix.validated_record prefix1 2#u8
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue vr2 =>
            let (r5, transcript3) ←
              packet
                aspis_coreDigest32Inst transcript2 vr2
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val2 =>
              let zc := Array.repeat 10#usize aspis_core.field.QM31.ZERO
              let r6 ← r1_wire.Prefix.validated_record prefix1 3#u8
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue vr3 =>
                let (r7, transcript4) ←
                  packet
                    aspis_coreDigest32Inst transcript3 vr3
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let (_, index_mut_back) ← Array.index_mut_usize zc 0#usize
                  let r8 ← r1_wire.Prefix.validated_record prefix1 4#u8
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue vr4 =>
                    let (r9, transcript5) ←
                      packet
                        aspis_coreDigest32Inst transcript4 vr4
                    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val4 =>
                      let zc1 := index_mut_back val3
                      let (_, index_mut_back1) ←
                        Array.index_mut_usize zc1 1#usize
                      begin5 packet aspis_coreDigest32Inst prefix1 transcript5 val val1 val2 val4 index_mut_back1
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      let r10 ←
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          r1_wire.Challenges (core.convert.FromSame
                          r1_wire.Error) residual
                      pure (r10, transcript5)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    let r9 ←
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        r1_wire.Challenges (core.convert.FromSame
                        r1_wire.Error) residual
                    pure (r9, transcript4)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r8 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                      residual
                  pure (r8, transcript4)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r7 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                    residual
                pure (r7, transcript3)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                  residual
              pure (r6, transcript3)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                residual
            pure (r5, transcript2)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
          pure (r4, transcript2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
        pure (r3, transcript1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
      pure (r2, transcript1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
    pure (r1, transcript)
end AspisR1.NHG_BeginPackets
namespace AspisR1.NHG_Begin
open AspisR1.NHG_BeginPackets

theorem source {H : Type} (D : aspis_core.Digest32 H)
 (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
 begin S1SemanticCode.semanticValidated D prefix1 transcript=
 S1SemanticCode.begin D prefix1 transcript := by
 rfl
#print axioms source
end AspisR1.NHG_Begin
