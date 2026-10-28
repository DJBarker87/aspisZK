import R1Z.ProverRwQueryCallerSplit
import R1Z.ProverRwQueryMaterialTransport
import R1Z.ProverRwQueryTrace
set_option autoImplicit false
namespace R1Z.ProverRwQueryComplete
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwQueryMaterial ProverRwQueryPublish ProverRwQueryFinishTransport
open ProverRwQueryMaterialTransport
variable [ExternalTypes] [ExternalFuns]

def publishFinite {H : Type} (self : host_transcript.Transcript H) (r : Output) :
    Result (core.result.Result Queries verifier.Error × host_transcript.Transcript H) :=
  match r with
  | .Ok (q,state) => do
    ProverRwQueryTrace.finite q 22 0#usize
    ok (.Ok q,{self with state:=state})
  | .Err e => ok (.Err e,self)

theorem publish_finite {H : Type} (self : host_transcript.Transcript H) (r : Output) :
    publish self r=publishFinite self r := by
  cases r with
  | Ok p =>
    rcases p with ⟨q,state⟩
    simp only [publish,publishFinite,ProverRwQueryTrace.trace_finite]
  | Err e => rfl

set_option backward.isDefEq.respectTransparency false in
theorem queries_policy {H : Type} (h : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    host_transcript.Transcript.queries h self row payload = (do
      let p ← materialize h self row payload
      let r ← ProverCommitQuery26.policy.queries p.2.1 p.2.2
      publish p.1 (policyResult r)) := by
  rw [ProverRwQueryCallerSplit.queries_factor]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro p hp
  rcases p with ⟨absorbed,blocks,advances⟩
  rw [ProverRwQueryPolicy.policy_transport]
  simp only [bind_assoc_eq,bind_tc_ok]

set_option backward.isDefEq.respectTransparency false in
theorem queries_complete {H : Type} (h : aspis_core.digest.Digest32 H)
    (self : OldState H Unit) (row : U8) (payload : Slice U8) :
    host_transcript.Transcript.queries h (erase self) row payload = (do
      let p ← ProverCommitQuery26.materialize (hash h) ProverCommitQuery26.policy self row payload
      let r ← ProverCommitQuery26.policy.queries p.2.1 p.2.2
      publishFinite (erase p.1) (policyResult r)) := by
  rw [queries_policy,materialize_transport]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro p hp
  rcases p with ⟨absorbed,blocks,advances⟩
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro r hr
  exact publish_finite _ _

#print axioms publish_finite
#print axioms queries_policy
#print axioms queries_complete
end R1Z.ProverRwQueryComplete
