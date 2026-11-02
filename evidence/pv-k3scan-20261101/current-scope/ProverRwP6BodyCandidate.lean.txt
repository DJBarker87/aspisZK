import R1Z.ProverRwP6BoundaryTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BodyCandidate
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := ProverRwP6BoundaryInstall.selected
-- The complete actual caller runs against the three new entries, with every
-- other retained dictionary operation, error, audit and returned store intact.
def execute (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :=
  ProverRwBodyNativeWideInstall.execute (selected ops)
    store pub compiled v hash binding digest attempt s

theorem serializer_total (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    ∃ bytes, (selected ops).op51 x = ok bytes := ProverRwP6FlatTotal.total x
theorem boundary_total (ops : ExternalFuns) (p : Array aspis_core.field.QM31 28#usize) :
    ∃ out, (selected ops).op120 p = ok out := ProverRwP6BoundaryTotal.total p
theorem transition_total (ops : ExternalFuns) (p : ProverRwP6TransitionTransport.Public) :
    ∃ out, (selected ops).op225 p = ok out := by cases p <;> exact ⟨_, rfl⟩
#print axioms serializer_total
#print axioms boundary_total
#print axioms transition_total
end R1Z.ProverRwP6BodyCandidate
