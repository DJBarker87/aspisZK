import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 23: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_r8 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) (vr2 : r1_wire.ValidatedRecord) (r7 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
 f_r8 c s alpha val1 val3 state_before_z0 transcript2 val4 vr2 r7 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let r8 ←
      c.c15 29#usize vr2 0#usize
    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
    match cf8 with
    | core.ops.control_flow.ControlFlow.Continue val5 =>
      let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r7
      match cf9 with
      | core.ops.control_flow.ControlFlow.Continue vr3 =>
        f_r9 c s alpha val1 val3 state_before_z0 transcript2 val4 val5 vr3
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame
          r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame
        r1_wire.Error) residual) := rfl
#print axioms occurrence_r8
end AspisR1.NNG_SourceSuffixes
