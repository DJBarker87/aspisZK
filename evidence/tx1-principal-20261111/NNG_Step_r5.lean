import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 12: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_r5 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (vr : r1_wire.ValidatedRecord) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
 f_r5 c s running val2 mask alpha transcript1 val1 vr r4 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let r5 ← c.c15 29#usize vr 87#usize
    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf4 with
    | core.ops.control_flow.ControlFlow.Continue val3 =>
      f_q1 c s running val2 mask alpha transcript1 val1 val3 r4
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
        residual) := rfl
#print axioms occurrence_r5
end AspisR1.NNG_SourceSuffixes
