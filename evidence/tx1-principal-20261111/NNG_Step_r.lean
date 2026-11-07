import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Fresh source occurrence 0: SAME typed values and complete Result continuation. Support until concrete child installation. -/
theorem occurrence_r {H W : Type} (c : Calls) (s : Parent H W) :
 f_r c s = (do
    let aspis_coredigestDigest32Inst := s.digest
    let public1 := s.publicValue
    let prefix1 := s.prefixValue
    let transcript := s.transcript
    let challenges := s.challenges
    let obs := s.observer
    let r ←
      c.c10 aspis_coredigestDigest32Inst prefix1 transcript
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (running, alpha, transcript1) := val
      f_mark2 c s running alpha transcript1
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual) := rfl
#print axioms occurrence_r
end AspisR1.NNG_SourceSuffixes
