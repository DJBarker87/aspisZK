import R1Z.PV_CurrentScaleInstall
import R1Z.PV_ProverRwP7BodyCoefficients
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CurrentScaleBody
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem caller (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :
    @prover.prove_masked_with_attempt _ (PV_CurrentScaleInstall.selected ops) S
      store pub compiled v hash context binding attempt s =
    @prover.prove_masked_with_attempt _ (PV_TraceValueInstall.selected ops) S
      store pub compiled v hash context binding attempt s := by
  rw [PV_CurrentScaleInstall.dictionary_preserved]
#print axioms caller
end R1Z.PV_CurrentScaleBody
