import R1Z.ProverRwQueryMaterial
set_option autoImplicit false
namespace R1Z.ProverRwQueryPublish
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
variable [ExternalTypes] [ExternalFuns]

def publish {H : Type} (self : host_transcript.Transcript H) (r : Output) :
    Result (core.result.Result Queries verifier.Error × host_transcript.Transcript H) :=
  match r with
  | .Ok (queries,state) => do
    host_transcript.trace_queries queries
    ok (.Ok queries,{self with state := state})
  | .Err error => ok (.Err error,self)


theorem branch_publish {H : Type} (self : host_transcript.Transcript H) (r : Output) :
    (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (q,state) := val
        host_transcript.trace_queries q
        ok (core.result.Result.Ok q,{self with state := state})
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array U32 22#usize) (core.convert.FromSame verifier.Error) residual
        ok (r1,self)) = publish self r := by
  cases r <;> rfl

#print axioms branch_publish
end R1Z.ProverRwQueryPublish
