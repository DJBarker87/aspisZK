import R1Z.ProverRwSuccessNativeWideInstall
import R1Z.ProverRwBodyErrorData
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwBodyNativeWideInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwOuterGuardLeaves.selected (ProverRwSuccessNativeWideInstall.selected ops)
theorem dictionary (ops : ExternalFuns) : selected ops=ProverRwBodyErrorData.selected ops :=
  congrArg ProverRwOuterGuardLeaves.selected (ProverRwSuccessNativeWideInstall.dictionary_preserved ops)

def execute (dict : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :=
  letI : ExternalFuns := dict
  prover.prove_masked_with_attempt store pub compiled v hash
    (ProverRwOuterContextModel.context digest attempt.mask_nonce) binding attempt s
-- Exact complete source Result, including errors, audit and returned store.
-- Equality with the abstract security model is still a separate open equation.
theorem body (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :
    execute (selected ops) store pub compiled v hash binding digest attempt s=
      execute (ProverRwBodyErrorData.selected ops) store pub compiled v hash binding digest attempt s := by
  rw [dictionary]
#print axioms dictionary
#print axioms body
end R1Z.ProverRwBodyNativeWideInstall
