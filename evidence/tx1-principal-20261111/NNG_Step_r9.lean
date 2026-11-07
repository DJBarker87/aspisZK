import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 24: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_r9 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (vr3 : r1_wire.ValidatedRecord) :
 f_r9 c s alpha val1 val3 state_before_z0 transcript2 val4 val5 vr3 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let (r9, transcript3) ←
      c.c13
        aspis_coredigestDigest32Inst transcript2 vr3
    let cf10 ←
      core.result.Result.Insts.CoreOpsTry.branch r9
    match cf10 with
    | core.ops.control_flow.ControlFlow.Continue val6 =>
      f_mark5 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame
        r1_wire.Error) residual) := rfl
#print axioms occurrence_r9
end AspisR1.NNG_SourceSuffixes
