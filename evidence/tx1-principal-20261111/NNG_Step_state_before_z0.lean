import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 20: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_state_before_z0 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
 f_state_before_z0 c s alpha transcript1 val1 val3 r4 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let state_before_z0 ←
      c.c14
        aspis_coredigestDigest32Inst transcript1
    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r4
    match cf5 with
    | core.ops.control_flow.ControlFlow.Continue vr1 =>
      f_r6 c s alpha transcript1 val1 val3 state_before_z0 vr1
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame
        r1_wire.Error) residual) := rfl
#print axioms occurrence_state_before_z0
end AspisR1.NNG_SourceSuffixes
