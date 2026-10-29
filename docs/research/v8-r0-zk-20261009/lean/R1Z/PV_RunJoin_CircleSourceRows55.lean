import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CircleSourceRows55
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

theorem first {H : Type} (D : aspis_core.digest.Digest32 H)
    (self : host_wire.SemanticTranscript H) (framed : Slice U8) :
    host_wire.SemanticTranscript.challenge_reference_circle_point D self 25#u8 framed=(do
      let (r,self1) ← host_wire.SemanticTranscript.sample_block D self 25#u8 framed
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val => do
        let scp ← sampler.circle_sample val aspis_core.r0_transcript.CircleRow.First
        ok (core.result.Result.Ok scp,self1)
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.circle.SecureCirclePoint (core.convert.FromSame r1_wire.Error) residual
        ok (r1,self1)) := rfl
#print axioms first

theorem second {H : Type} (D : aspis_core.digest.Digest32 H)
    (self : host_wire.SemanticTranscript H) (framed : Slice U8) :
    host_wire.SemanticTranscript.challenge_reference_circle_point D self 26#u8 framed=(do
      let (r,self1) ← host_wire.SemanticTranscript.sample_block D self 26#u8 framed
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val => do
        let scp ← sampler.circle_sample val aspis_core.r0_transcript.CircleRow.Second
        ok (core.result.Result.Ok scp,self1)
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.circle.SecureCirclePoint (core.convert.FromSame r1_wire.Error) residual
        ok (r1,self1)) := rfl
#print axioms second
end R1Z.PV_RunJoin_CircleSourceRows55
