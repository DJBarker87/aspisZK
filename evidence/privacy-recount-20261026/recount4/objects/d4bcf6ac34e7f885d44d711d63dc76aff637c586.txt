import R1Z.ProverRwBodyStore
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwBodyDataCriterion
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore

def data {A S : Type} : Result (A × S) → Result A
  | .ok (a,_) => .ok a
  | .fail e => .fail e
  | .div => .div

theorem eq_of_data {A S : Type} (after : S) (left right : Result (A × S))
    (hl : Keeps after left) (hr : Keeps after right) (same : data left=data right) : left=right := by
  cases left with
  | ok p =>
    rcases p with ⟨a,s⟩
    cases right with
    | ok q =>
      rcases q with ⟨b,t⟩
      change s=after at hl
      change t=after at hr
      have hab : a=b := Result.ok.inj same
      cases hab
      cases hl
      cases hr
      rfl
    | fail e => cases same
    | div => cases same
  | fail e =>
    cases right with
    | ok p => cases same
    | fail e' => exact congrArg Result.fail (Result.fail.inj same)
    | div => cases same
  | div =>
    cases right with
    | ok p => cases same
    | fail e => cases same
    | div => rfl

variable [ExternalTypes] [ExternalFuns]
theorem continuation {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (binding : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (r : core.result.Result
      (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
        aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) (after : S)
    (model : Result ((core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error) × S))
    (model_state : Keeps after model)
    (model_data : data (ProverRwBodyStoreSource.afterReserve store pub compiled v hash context binding attempt r after)=data model) :
    ProverRwBodyStoreSource.afterReserve store pub compiled v hash context binding attempt r after=model :=
  eq_of_data after _ model
    (ProverRwBodyStore.continuation store pub compiled v hash context binding attempt r after) model_state model_data
#print axioms eq_of_data
#print axioms continuation
end R1Z.ProverRwBodyDataCriterion
