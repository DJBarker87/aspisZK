import NHG_Begin9
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode (Code)
namespace AspisR1.NHG_BeginPackets
def begin5 {H : Type} (packet : aspis_core.Digest32 H → r1_wire.SemanticTranscript H → r1_wire.ValidatedRecord → Code ((core.result.Result aspis_core.field.QM31 r1_wire.Error) × r1_wire.SemanticTranscript H)) (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript5 : r1_wire.SemanticTranscript H)
  (val val1 val2 val4 : aspis_core.field.QM31)
  (index_mut_back1 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
  Code ((core.result.Result r1_wire.Challenges r1_wire.Error) × r1_wire.SemanticTranscript H)
  := do
  let r10 ← r1_wire.Prefix.validated_record prefix1 5#u8
  let cf10 ←
    core.result.Result.Insts.CoreOpsTry.branch r10
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue vr5 =>
    let (r11, transcript6) ←
      packet
        aspis_coreDigest32Inst transcript5 vr5
    let cf11 ←
      core.result.Result.Insts.CoreOpsTry.branch r11
    match cf11 with
    | core.ops.control_flow.ControlFlow.Continue val5 =>
      let zc2 := index_mut_back1 val4
      let (_, index_mut_back2) ←
        Array.index_mut_usize zc2 2#usize
      let r12 ←
        r1_wire.Prefix.validated_record prefix1 6#u8
      let cf12 ←
        core.result.Result.Insts.CoreOpsTry.branch r12
      match cf12 with
      | core.ops.control_flow.ControlFlow.Continue vr6 =>
        let (r13, transcript7) ←
          packet
            aspis_coreDigest32Inst transcript6 vr6
        let cf13 ←
          core.result.Result.Insts.CoreOpsTry.branch r13
        match cf13 with
        | core.ops.control_flow.ControlFlow.Continue val6
          =>
          let zc3 := index_mut_back2 val5
          let (_, index_mut_back3) ←
            Array.index_mut_usize zc3 3#usize
          let r14 ←
            r1_wire.Prefix.validated_record prefix1 7#u8
          let cf14 ←
            core.result.Result.Insts.CoreOpsTry.branch r14
          match cf14 with
          | core.ops.control_flow.ControlFlow.Continue vr7
            =>
            let (r15, transcript8) ←
              packet
                aspis_coreDigest32Inst transcript7 vr7
            let cf15 ←
              core.result.Result.Insts.CoreOpsTry.branch
                r15
            match cf15 with
            | core.ops.control_flow.ControlFlow.Continue
              val7 =>
              let zc4 := index_mut_back3 val6
              let (_, index_mut_back4) ←
                Array.index_mut_usize zc4 4#usize
              let r16 ←
                r1_wire.Prefix.validated_record prefix1
                  8#u8
              let cf16 ←
                core.result.Result.Insts.CoreOpsTry.branch
                  r16
              match cf16 with
              | core.ops.control_flow.ControlFlow.Continue
                vr8 =>
                let (r17, transcript9) ←
                  packet
                    aspis_coreDigest32Inst transcript8 vr8
                let cf17 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r17
                match cf17 with
                |
                  core.ops.control_flow.ControlFlow.Continue
                  val8 =>
                  let zc5 := index_mut_back4 val7
                  let (_, index_mut_back5) ←
                    Array.index_mut_usize zc5 5#usize
                  begin9 packet aspis_coreDigest32Inst prefix1 transcript9 val val1 val2 val8 index_mut_back5
                | core.ops.control_flow.ControlFlow.Break
                  residual =>
                  let r18 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_wire.Challenges
                      (core.convert.FromSame r1_wire.Error)
                      residual
                  pure (r18, transcript9)
              | core.ops.control_flow.ControlFlow.Break
                residual =>
                let r17 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_wire.Challenges
                    (core.convert.FromSame r1_wire.Error)
                    residual
                pure (r17, transcript8)
            | core.ops.control_flow.ControlFlow.Break
              residual =>
              let r16 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_wire.Challenges (core.convert.FromSame
                  r1_wire.Error) residual
              pure (r16, transcript8)
          | core.ops.control_flow.ControlFlow.Break
            residual =>
            let r15 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_wire.Challenges (core.convert.FromSame
                r1_wire.Error) residual
            pure (r15, transcript7)
        | core.ops.control_flow.ControlFlow.Break residual
          =>
          let r14 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges (core.convert.FromSame
              r1_wire.Error) residual
          pure (r14, transcript7)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r13 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges (core.convert.FromSame
            r1_wire.Error) residual
        pure (r13, transcript6)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r12 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges (core.convert.FromSame
          r1_wire.Error) residual
      pure (r12, transcript6)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r11 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges (core.convert.FromSame
        r1_wire.Error) residual
    pure (r11, transcript5)
end AspisR1.NHG_BeginPackets
namespace AspisR1.NHG_Begin5
open AspisR1.NHG_BeginPackets

theorem source {H : Type} (D : aspis_core.Digest32 H)
 (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) (val val1 val2 valN : aspis_core.field.QM31)
 (back : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
 begin5 S1SemanticCode.semanticValidated D prefix1 transcript val val1 val2 valN back=
 S1SemanticCode.begin5 D prefix1 transcript val val1 val2 valN back := by
 rfl
#print axioms source
end AspisR1.NHG_Begin5
