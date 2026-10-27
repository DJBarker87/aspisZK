import R1Z.ProverRw18ContextJoin
import R1Z.PV_RW_CombinedBodyData
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextCaller
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- Caller transport with the source and context identities still explicit.
theorem caller (ops : ExternalFuns) (extracted : ProverRw18ContextJoin.Compression)
    (source_law : ops.op223=extracted)
    (context_identity : extracted =
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops))
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
  rw [ProverRw18ContextJoin.dictionaries ops extracted source_law context_identity]
  rfl

#print axioms caller
end R1Z.ProverRw18ContextCaller
