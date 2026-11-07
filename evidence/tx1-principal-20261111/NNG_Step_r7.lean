import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 22: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_r7 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) :
 f_r7 c s alpha val1 val3 state_before_z0 transcript2 val4 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let r7 ← c.c11 prefix1 26#u8
    let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
    match cf7 with
    | core.ops.control_flow.ControlFlow.Continue vr2 =>
      f_r8 c s alpha val1 val3 state_before_z0 transcript2 val4 vr2 r7
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame
        r1_wire.Error) residual) := rfl
#print axioms occurrence_r7
end AspisR1.NNG_SourceSuffixes
