import R1Z.ProverRw19P6Join
import R1Z.PV_RW_CombinedBodyData
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19P6Caller
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- Concrete P6 caller transport. The single remaining source law is explicit.
theorem caller (ops : ExternalFuns)
    (P_source_p6 : ops.op223 =
      @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops))
    {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :
    ProverRwP6BodyStore.execute (ProverRw18ContextJoin.original ops)
      store pub compiled v hash binding digest attempt s =
    ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
      store pub compiled v hash binding digest attempt s := by
  rw [ProverRw19P6Join.dictionaries ops P_source_p6]
  rfl

#print axioms caller
end R1Z.ProverRw19P6Caller
