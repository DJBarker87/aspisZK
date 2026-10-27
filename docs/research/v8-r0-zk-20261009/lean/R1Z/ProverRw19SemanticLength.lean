import R1Z.ProverRw19PublishLength
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19SemanticLength
open Aeneas Aeneas.Std Result ProverRwFull ProverRw19ByteLength
variable [ExternalTypes] [ExternalFuns]

theorem proof (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (size : Usize) (P_proof_size : compact.PROOF_BYTES = ok size) :
    HasLength size.val
      (prover.prove_from_semantics pub variant hash backend sem (reserved,context)) := by
  unfold prover.prove_from_semantics
  repeat' first
    | exact ProverRw19PublishLength.publish _ _ size P_proof_size
    | exact residual _ _
    | apply bind_good; intro x
    | dsimp only [Aeneas.Std.uncurry]
    | split

#print axioms proof
end R1Z.ProverRw19SemanticLength
