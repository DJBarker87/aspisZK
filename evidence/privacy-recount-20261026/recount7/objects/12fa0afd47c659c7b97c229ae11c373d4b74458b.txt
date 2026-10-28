import R1Z.ProverRwP7BodyCloneSource
import R1Z.ProverRwP7FibreWide
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7BodyFibre
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
variable (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)

theorem continuation
    (r : core.result.Result
      (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
        aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) (after : S) :
    letI : ExternalFuns := ProverRwP7FibreInstall.selected ops
    ProverRwBodyStoreSource.afterReserve store pub compiled v hash context binding attempt r after =
      ProverRwP7BodyCloneSource.afterReserve store pub compiled v hash context binding attempt r after := by
  letI : ExternalFuns := ProverRwP7FibreInstall.selected ops
  unfold ProverRwBodyStoreSource.afterReserve ProverRwP7BodyCloneSource.afterReserve
  simp only [aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone,
    ProverRwP7FibreInstall.clone_preserved]
  rfl

theorem caller (s : S) :
    letI : ExternalFuns := ProverRwP7FibreInstall.selected ops
    prover.prove_masked_with_attempt store pub compiled v hash context binding attempt s =
      (do
        let (r,after) ← aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
          store attempt hash binding context s
        ProverRwP7BodyCloneSource.afterReserve store pub compiled v hash context binding attempt r after) := by
  letI : ExternalFuns := ProverRwP7FibreInstall.selected ops
  rw [ProverRwBodyStore.factor]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair _
  rcases pair with ⟨r,after⟩
  exact continuation ops store pub compiled v hash context binding attempt r after
#print axioms continuation
#print axioms caller
end R1Z.ProverRwP7BodyFibre
