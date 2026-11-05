import NHG_Lengths
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode (Code)
namespace AspisR1.NHG_BeginPackets
def begin13 {H : Type} (packet : aspis_core.Digest32 H → r1_wire.SemanticTranscript H → r1_wire.ValidatedRecord → Code ((core.result.Result aspis_core.field.QM31 r1_wire.Error) × r1_wire.SemanticTranscript H)) (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript13 : r1_wire.SemanticTranscript H)
  (val val1 val2 val12 : aspis_core.field.QM31)
  (index_mut_back9 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
  Code ((core.result.Result r1_wire.Challenges r1_wire.Error) × r1_wire.SemanticTranscript H)
  := do
  let r26 ←
    r1_wire.Prefix.validated_record
      prefix1 13#u8
  let cf26 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r26
  match cf26 with
  |
    core.ops.control_flow.ControlFlow.Continue
    vr13 =>
    let (r27, transcript14)
      ←
      packet
        aspis_coreDigest32Inst
        transcript13 vr13
    let cf27 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r27
    match cf27 with
    |
      core.ops.control_flow.ControlFlow.Continue
      val13 =>
      let r28 ←
        r1_wire.Prefix.validated_record
          prefix1 14#u8
      let cf28 ←
        core.result.Result.Insts.CoreOpsTry.branch
          r28
      match cf28 with
      |
        core.ops.control_flow.ControlFlow.Continue
        vr14 =>
        let (r29,
          transcript15) ←
          packet
            aspis_coreDigest32Inst
            transcript14
            vr14
        let cf29 ←
          core.result.Result.Insts.CoreOpsTry.branch
            r29
        match cf29 with
        |
          core.ops.control_flow.ControlFlow.Continue
          val14 =>
          let zc10 :=
            index_mut_back9
              val12
          pure
            (core.result.Result.Ok
            {
              lambda := val,
              chi := val1,
              theta := val2,
              zc := zc10,
              mu := val13,
              eta := val14
            },
            transcript15)
        |
          core.ops.control_flow.ControlFlow.Break
          residual =>
          let r30 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges
              (core.convert.FromSame
              r1_wire.Error)
              residual
          pure (r30,
            transcript15)
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r29 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges
            (core.convert.FromSame
            r1_wire.Error)
            residual
        pure (r29,
          transcript14)
    |
      core.ops.control_flow.ControlFlow.Break
      residual =>
      let r28 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges
          (core.convert.FromSame
          r1_wire.Error)
          residual
      pure (r28,
        transcript14)
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    let r27 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges
        (core.convert.FromSame
        r1_wire.Error)
        residual
    pure (r27, transcript13)
end AspisR1.NHG_BeginPackets
namespace AspisR1.NHG_Begin13
open AspisR1.NHG_BeginPackets

theorem source {H : Type} (D : aspis_core.Digest32 H)
 (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) (val val1 val2 valN : aspis_core.field.QM31)
 (back : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
 begin13 S1SemanticCode.semanticValidated D prefix1 transcript val val1 val2 valN back=
 S1SemanticCode.begin13 D prefix1 transcript val val1 val2 valN back := by
 rfl
#print axioms source
end AspisR1.NHG_Begin13
