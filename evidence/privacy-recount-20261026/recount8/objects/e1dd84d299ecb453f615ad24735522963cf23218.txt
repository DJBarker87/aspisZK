import R1Z.ProverRwQueryStop
set_option autoImplicit false
namespace R1Z.ProverRwQueryFinishTransport
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwQueryStop Query31ExplicitScanBody

def rawResult : core.result.Result (Queries × Array U8 32#usize)
    AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError → Output
  | .Ok v => .Ok v
  | .Err _ => .Err verifier.Error.Transcript

def policyResult : core.result.Result (Queries × Array U8 32#usize)
    AspisR1SimControl21.verifier.Error → Output
  | .Ok v => .Ok v
  | .Err _ => .Err verifier.Error.Transcript

theorem finish_transport (advances : Blocks) (k : Usize) (s : CurrentScan) :
    (AspisR1Query31Transcript.finishAdvance advances k s >>= fun r => ok (rawResult r))=
      finishAt advances k s := by
  unfold AspisR1Query31Transcript.finishAdvance
    AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish
  simp only [AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT]
  by_cases full : s.accepted_len=22#usize
  · simp only [full,if_true,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
      bind_assoc_eq,finishAt]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro v hv
    rfl
  · simp only [full,if_false,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      rawResult,finishAt]

theorem query_transport (blocks advances : Blocks) :
    (ProverCommitQuery26.policy.queries blocks advances >>= fun r => ok (policyResult r)) =
    (ProverCommitQuery26.raw blocks advances >>= fun r => ok (rawResult r)) := by
  change ((do let r ← ProverCommitQuery26.raw blocks advances
              match r with
              | .Ok v => ok (core.result.Result.Ok v)
              | .Err _ => ok (core.result.Result.Err AspisR1SimControl21.verifier.Error.Transcript)) >>= _) = _
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro r hr
  cases r <;> rfl

#print axioms finish_transport
#print axioms query_transport
end R1Z.ProverRwQueryFinishTransport
