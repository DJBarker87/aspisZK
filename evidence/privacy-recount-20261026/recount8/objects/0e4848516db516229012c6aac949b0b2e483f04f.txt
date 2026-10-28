import R1Z.ProverRwQueryComplete
set_option autoImplicit false
namespace R1Z.ProverRwQueryInstalled
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwQueryMaterial ProverRwQueryFinishTransport ProverRwQueryComplete
variable [ExternalTypes] [ExternalFuns]

def query {H : Type} (h : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) := do
  let p ← materialize h self row payload
  let r ← ProverCommitQuery26.policy.queries p.2.1 p.2.2
  publishFinite p.1 (policyResult r)

set_option backward.isDefEq.respectTransparency false in
theorem query_exact {H : Type} (h : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    host_transcript.Transcript.queries h self row payload=query h self row payload := by
  rw [queries_policy]
  unfold query
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro p hp
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro r hr
  exact publish_finite _ _

#print axioms query_exact
end R1Z.ProverRwQueryInstalled
