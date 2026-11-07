import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 11: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_r4 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) :
 f_r4 c s running val2 mask alpha transcript1 val1 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let r4 ← c.c11 prefix1 25#u8
    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
    match cf3 with
    | core.ops.control_flow.ControlFlow.Continue vr =>
      f_r5 c s running val2 mask alpha transcript1 val1 vr r4
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
        residual) := rfl
#print axioms occurrence_r4
end AspisR1.NNG_SourceSuffixes
