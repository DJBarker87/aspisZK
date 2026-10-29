import R1Z.PV_RunJoin_PublishReach54
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceSuccessVariant55
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

theorem s1 (hash : aspis_core.digest.LegacyHashFn) (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
    prover.prepare_opening .S1 hash backend sem=ok (.Err verifier.Error.Semantic) := rfl

theorem d (hash : aspis_core.digest.LegacyHashFn) (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
    prover.prepare_opening .D hash backend sem=ok (.Err verifier.Error.Semantic) := rfl

theorem complete (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn) (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (salts : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets × aspis_core.state_only_hiding.StateOnlyHidingContext)
    (proof : alloc.vec.Vec U8)
    (success : prover.prove_from_semantics public1 variant hash backend sem salts=ok (.Ok proof)) : variant=.S2 := by
  obtain ⟨prepared,ps,p,hp,hs,hf,hpub⟩ := PV_RunJoin_PublishReach54.complete public1 variant hash backend sem salts proof success
  cases variant with
  | S2 => rfl
  | S1 => rw [s1] at hp;cases hp
  | D => rw [d] at hp;cases hp
#print axioms s1
#print axioms d
#print axioms complete
end R1Z.PV_RunJoin_SourceSuccessVariant55
