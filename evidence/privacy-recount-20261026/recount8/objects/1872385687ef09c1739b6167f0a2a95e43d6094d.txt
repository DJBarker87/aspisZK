import R1Z.ProverRwBodyStoreSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwBodyStore
open Aeneas Aeneas.Std Result ProverRwFull

def Keeps {A S : Type} (s : S) : Result (A × S) → Prop
  | .ok (_,after) => after=s
  | .fail _ | .div => True

theorem ok_keeps {A S : Type} (s : S) (a : A) : Keeps s (.ok (a,s)) := rfl

theorem bind_keeps {A B S : Type} (s : S) (r : Result A) (f : A → Result (B × S))
    (hf : ∀ a,Keeps s (f a)) : Keeps s (r >>= f) := by
  cases r with
  | ok a => exact hf a
  | fail e => trivial
  | div => trivial

variable [ExternalTypes] [ExternalFuns]
variable {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)

theorem factor (s : S) : prover.prove_masked_with_attempt store pub compiled v hash context binding attempt s=
    (do
      let (r,after) ← aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
        store attempt hash binding context s
      ProverRwBodyStoreSource.afterReserve store pub compiled v hash context binding attempt r after) := by
  unfold prover.prove_masked_with_attempt ProverRwBodyStoreSource.afterReserve
  rfl

/-- Every returned status (successful or rejected) carries the exact supplied
reservation writeback. Failure/divergence has no returned source state; this
predicate makes no native crash/durability assertion about those cases. -/
theorem continuation
    (r : core.result.Result
      (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
        aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) (after : S) :
    Keeps after (ProverRwBodyStoreSource.afterReserve store pub compiled v hash context binding attempt r after) := by
  unfold ProverRwBodyStoreSource.afterReserve
  repeat' first
    | exact ok_keeps _ _
    | apply bind_keeps; intro x
    | dsimp only [Aeneas.Std.uncurry]
    | split
#print axioms ok_keeps
#print axioms bind_keeps
#print axioms factor
#print axioms continuation
end R1Z.ProverRwBodyStore
