import R1Z.PV_RunJoin_NativeControl55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePhaseSource55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
variable [ExternalTypes] [ExternalFuns]
attribute [local irreducible] prover.prove_from_semantics

theorem complete (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) :
    source ⟨public1,variant,hash,backend,sem,(reserved,context)⟩=
      prover.prove_from_semantics public1 variant hash backend sem (reserved,context) := rfl
#print axioms complete
end R1Z.PV_RunJoin_NativePhaseSource55
