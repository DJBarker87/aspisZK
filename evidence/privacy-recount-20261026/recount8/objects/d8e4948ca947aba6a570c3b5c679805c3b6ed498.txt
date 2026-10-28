import R1Z.ProverRwP6PowersTotal
import R1Z.ProverRwBodyDataCriterion
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BodyStore
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwOuterGuardLeaves.selected (ProverRwP6PowersInstall.selected ops)
def execute (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :=
  ProverRwBodyNativeWideInstall.execute (selected ops)
    store pub compiled v hash binding digest attempt s

theorem writeback (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after)) :
    Keeps after (execute ops store pub compiled v hash binding digest attempt s) :=
  ProverRwBodyReservationTransport.body_writeback (ProverRwP6PowersInstall.selected ops)
    store pub compiled v hash binding digest attempt s after accepted reservation

theorem powers_total (ops : ExternalFuns) (N : Usize) (x : aspis_core.field.wide_exact.WideExact) :
    ∃ out, (selected ops).op254 N x = ok out := ProverRwP6PowersTotal.total ops N x
#print axioms writeback
#print axioms powers_total
end R1Z.ProverRwP6BodyStore
