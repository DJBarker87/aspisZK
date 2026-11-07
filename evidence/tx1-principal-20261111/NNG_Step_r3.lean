import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 4: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_r3 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (r2 : core.result.Result Q aspis_core.state_only_prefix.r0.Error) :
 f_r3 c s running alpha transcript1 val1 r2 = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let r3 ←
      c.c1
        (r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        aspis_coredigestDigest32Inst) r2 ()
    let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      f_mark3 c s running val2 alpha transcript1 val1
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
        residual) := rfl
#print axioms occurrence_r3
end AspisR1.NNG_SourceSuffixes
