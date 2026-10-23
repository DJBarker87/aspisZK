import ActualSemanticRoundSourceModelV1

set_option autoImplicit false
namespace AspisR1ActualSemanticRoundSourceOwnerLinkV1

open AspisR1ActualSemanticRoundSourceModelV1
open Aeneas Aeneas.Std Result ControlFlow Error

/-- Attempt26's emitted round body, with precisely its four external method
slots parameterized. The source-owner source pin records the substitutions. -/
def emittedRound {H : Type} (B : Hooks)
    (D : AspisR1ActualSemanticRoundCutV1.aspis_core.digest.Digest32 H)
    (pref : AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix)
    (transcript : AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
    (alpha : Array QM 10#usize) (running : QM) (round : Usize) :
    Result (core.result.Result (QM × (Array QM 10#usize) ×
      AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
      AspisR1ActualSemanticRoundCutV1.r1_wire.Error) := do
  let i ← lift (UScalar.cast .U8 round)
  let row ← lift (Std.U8.wrapping_add 15#u8 i)
  let r ← AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix.validated_record pref row
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let r1 ← B.decode 28#usize vr 0#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let boundary ← B.boundary val
      let b ← B.neq boundary running
      if b then ok (core.result.Result.Err
          (AspisR1ActualSemanticRoundCutV1.r1_wire.Error.Boundary round)) else
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue vr1 =>
          let (r2, transcript1) ←
            AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript.semantic_validated
              D transcript vr1
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            let alpha1 ← Array.update alpha round val1
            let value ← B.value val alpha1 round
            ok (core.result.Result.Ok (value, alpha1, transcript1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (QM × (Array QM 10#usize) ×
                AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
              (core.convert.FromSame AspisR1ActualSemanticRoundCutV1.r1_wire.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (QM × (Array QM 10#usize) ×
              AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
            (core.convert.FromSame AspisR1ActualSemanticRoundCutV1.r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (QM × (Array QM 10#usize) ×
          AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
        (core.convert.FromSame AspisR1ActualSemanticRoundCutV1.r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (QM × (Array QM 10#usize) ×
        AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
      (core.convert.FromSame AspisR1ActualSemanticRoundCutV1.r1_wire.Error) residual

theorem source_model_eq_parameterized_emission
    {H : Type} (B : Hooks)
    (D : AspisR1ActualSemanticRoundCutV1.aspis_core.digest.Digest32 H)
    (pref : AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix)
    (transcript : AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
    (alpha : Array QM 10#usize) (running : QM) (round : Usize) :
    semanticRound B D pref transcript alpha running round =
      emittedRound B D pref transcript alpha running round := by
  rfl

#print axioms source_model_eq_parameterized_emission
end AspisR1ActualSemanticRoundSourceOwnerLinkV1
