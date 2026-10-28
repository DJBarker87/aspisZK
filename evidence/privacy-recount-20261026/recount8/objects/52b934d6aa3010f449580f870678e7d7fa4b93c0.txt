import R1Z.ProverRwP6TransitionSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6TransitionTransport
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
namespace Raw
abbrev Public := ProverRwP6TransitionSource.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Transfer := ProverRwP6TransitionSource.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := ProverRwP6TransitionSource.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
end Raw
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Late := aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
-- This implementation never inspects the opaque payment payload.
def transition (p : Public) : Result Late :=
  match p with
  | .Transfer _ t => ok t
  | .Withdrawal _ t => ok t

def mapPublic
    (transfer : Raw.Transfer → aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (withdrawal : Raw.Withdrawal → aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (p : Raw.Public) : Public :=
  match p with
  | .Transfer x t => .Transfer (transfer x) t
  | .Withdrawal x t => .Withdrawal (withdrawal x) t

-- Arbitrary payload maps: no field equations, representation bijection,
-- canonicality, or successful-output premise is required for this projection.
theorem transport
    (transfer : Raw.Transfer → aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (withdrawal : Raw.Withdrawal → aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (p : Raw.Public) :
    transition (mapPublic transfer withdrawal p) = ProverRwP6TransitionSource.transition p := by
  cases p <;> rfl

theorem transfer (p : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (t : Late) : transition (.Transfer p t) = ok t := rfl
theorem withdrawal (p : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (t : Late) : transition (.Withdrawal p t) = ok t := rfl
#print axioms transport
#print axioms transfer
#print axioms withdrawal
end R1Z.ProverRwP6TransitionTransport
