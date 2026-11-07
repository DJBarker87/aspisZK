import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 21: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_r6 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (vr1 : r1_wire.ValidatedRecord) :
 f_r6 c s alpha transcript1 val1 val3 state_before_z0 vr1 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let (r6, transcript2) ←
      c.c13
        aspis_coredigestDigest32Inst transcript1 vr1
    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
    match cf6 with
    | core.ops.control_flow.ControlFlow.Continue val4 =>
      f_r7 c s alpha val1 val3 state_before_z0 transcript2 val4
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame
        r1_wire.Error) residual) := rfl
#print axioms occurrence_r6
end AspisR1.NNG_SourceSuffixes
