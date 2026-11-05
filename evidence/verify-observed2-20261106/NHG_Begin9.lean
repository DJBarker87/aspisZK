import NHG_Begin13
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode (Code)
namespace AspisR1.NHG_BeginPackets
def begin9 {H : Type} (packet : aspis_core.Digest32 H → r1_wire.SemanticTranscript H → r1_wire.ValidatedRecord → Code ((core.result.Result aspis_core.field.QM31 r1_wire.Error) × r1_wire.SemanticTranscript H)) (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript9 : r1_wire.SemanticTranscript H)
  (val val1 val2 val8 : aspis_core.field.QM31)
  (index_mut_back5 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
  Code ((core.result.Result r1_wire.Challenges r1_wire.Error) × r1_wire.SemanticTranscript H)
  := do
  let r18 ←
    r1_wire.Prefix.validated_record prefix1
      9#u8
  let cf18 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r18
  match cf18 with
  |
    core.ops.control_flow.ControlFlow.Continue
    vr9 =>
    let (r19, transcript10) ←
      packet
        aspis_coreDigest32Inst transcript9
        vr9
    let cf19 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r19
    match cf19 with
    |
      core.ops.control_flow.ControlFlow.Continue
      val9 =>
      let zc6 := index_mut_back5 val8
      let (_, index_mut_back6) ←
        Array.index_mut_usize zc6 6#usize
      let r20 ←
        r1_wire.Prefix.validated_record
          prefix1 10#u8
      let cf20 ←
        core.result.Result.Insts.CoreOpsTry.branch
          r20
      match cf20 with
      |
        core.ops.control_flow.ControlFlow.Continue
        vr10 =>
        let (r21, transcript11) ←
          packet
            aspis_coreDigest32Inst
            transcript10 vr10
        let cf21 ←
          core.result.Result.Insts.CoreOpsTry.branch
            r21
        match cf21 with
        |
          core.ops.control_flow.ControlFlow.Continue
          val10 =>
          let zc7 := index_mut_back6 val9
          let (_, index_mut_back7) ←
            Array.index_mut_usize zc7
              7#usize
          let r22 ←
            r1_wire.Prefix.validated_record
              prefix1 11#u8
          let cf22 ←
            core.result.Result.Insts.CoreOpsTry.branch
              r22
          match cf22 with
          |
            core.ops.control_flow.ControlFlow.Continue
            vr11 =>
            let (r23, transcript12) ←
              packet
                aspis_coreDigest32Inst
                transcript11 vr11
            let cf23 ←
              core.result.Result.Insts.CoreOpsTry.branch
                r23
            match cf23 with
            |
              core.ops.control_flow.ControlFlow.Continue
              val11 =>
              let zc8 :=
                index_mut_back7 val10
              let (_, index_mut_back8) ←
                Array.index_mut_usize zc8
                  8#usize
              let r24 ←
                r1_wire.Prefix.validated_record
                  prefix1 12#u8
              let cf24 ←
                core.result.Result.Insts.CoreOpsTry.branch
                  r24
              match cf24 with
              |
                core.ops.control_flow.ControlFlow.Continue
                vr12 =>
                let (r25, transcript13) ←
                  packet
                    aspis_coreDigest32Inst
                    transcript12 vr12
                let cf25 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r25
                match cf25 with
                |
                  core.ops.control_flow.ControlFlow.Continue
                  val12 =>
                  let zc9 :=
                    index_mut_back8 val11
                  let (_, index_mut_back9)
                    ←
                    Array.index_mut_usize
                      zc9 9#usize
                  begin13 packet aspis_coreDigest32Inst prefix1 transcript13 val val1 val2 val12 index_mut_back9
                |
                  core.ops.control_flow.ControlFlow.Break
                  residual =>
                  let r26 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_wire.Challenges
                      (core.convert.FromSame
                      r1_wire.Error)
                      residual
                  pure (r26, transcript13)
              |
                core.ops.control_flow.ControlFlow.Break
                residual =>
                let r25 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_wire.Challenges
                    (core.convert.FromSame
                    r1_wire.Error) residual
                pure (r25, transcript12)
            |
              core.ops.control_flow.ControlFlow.Break
              residual =>
              let r24 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_wire.Challenges
                  (core.convert.FromSame
                  r1_wire.Error) residual
              pure (r24, transcript12)
          |
            core.ops.control_flow.ControlFlow.Break
            residual =>
            let r23 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_wire.Challenges
                (core.convert.FromSame
                r1_wire.Error) residual
            pure (r23, transcript11)
        |
          core.ops.control_flow.ControlFlow.Break
          residual =>
          let r22 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges
              (core.convert.FromSame
              r1_wire.Error) residual
          pure (r22, transcript11)
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r21 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges
            (core.convert.FromSame
            r1_wire.Error) residual
        pure (r21, transcript10)
    |
      core.ops.control_flow.ControlFlow.Break
      residual =>
      let r20 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges
          (core.convert.FromSame
          r1_wire.Error) residual
      pure (r20, transcript10)
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    let r19 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges
        (core.convert.FromSame
        r1_wire.Error) residual
    pure (r19, transcript9)
end AspisR1.NHG_BeginPackets
namespace AspisR1.NHG_Begin9
open AspisR1.NHG_BeginPackets

theorem source {H : Type} (D : aspis_core.Digest32 H)
 (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) (val val1 val2 valN : aspis_core.field.QM31)
 (back : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
 begin9 S1SemanticCode.semanticValidated D prefix1 transcript val val1 val2 valN back=
 S1SemanticCode.begin9 D prefix1 transcript val val1 val2 valN back := by
 rfl
#print axioms source
end AspisR1.NHG_Begin9
