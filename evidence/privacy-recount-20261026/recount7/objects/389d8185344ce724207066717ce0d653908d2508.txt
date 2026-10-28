import R1Z.ProverRwP6TransitionTransport
import R1Z.ProverRwBodyNativeWideInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6TransitionInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwBodyNativeWideInstall.selected ops with op225 := ProverRwP6TransitionTransport.transition}

theorem source (ops : ExternalFuns)
    (transfer : ProverRwP6TransitionTransport.Raw.Transfer → aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (withdrawal : ProverRwP6TransitionTransport.Raw.Withdrawal → aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (p : ProverRwP6TransitionTransport.Raw.Public) :
    (selected ops).op225 (ProverRwP6TransitionTransport.mapPublic transfer withdrawal p) =
      ProverRwP6TransitionSource.transition p := ProverRwP6TransitionTransport.transport transfer withdrawal p

-- Pointwise elimination avoids normalising the entire 262-entry dictionary.
theorem callback_removed (ops : ExternalFuns)
    (callback : ProverRwP6TransitionTransport.Public → Result ProverRwP6TransitionTransport.Late)
    (p : ProverRwP6TransitionTransport.Public) :
    (selected {ops with op225 := callback}).op225 p = (selected ops).op225 p := rfl

def execute (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :=
  ProverRwBodyNativeWideInstall.execute (selected ops)
    store pub compiled v hash binding digest attempt s
#print axioms source
#print axioms callback_removed
end R1Z.ProverRwP6TransitionInstall
