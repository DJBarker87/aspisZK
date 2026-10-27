import R1Z.ProverRw19BodyLength
import R1Z.ProverRw19SelectedProofSize
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19SelectedBodyLength
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- The auxiliary size-callback premise is discharged for the original caller.
-- This is a length invariant, not the complete proof-byte equation.
theorem original (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :
    ProverRw19BodyLengthValue.HasLength 57607 (ProverRwP6BodyStore.execute (ProverRw18ContextJoin.original ops) store pub compiled v hash binding digest attempt s) :=
  @ProverRw19BodyLength.body _
    (ProverRwP6BodyStore.selected (ProverRw18ContextJoin.original ops)) S
    store pub compiled v hash (ProverRwOuterContextModel.context digest attempt.mask_nonce)
    binding attempt s 57607#usize (ProverRw19SelectedProofSize.original ops)

#print axioms original
end R1Z.ProverRw19SelectedBodyLength
