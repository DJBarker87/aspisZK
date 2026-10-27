import R1Z.PV_CB3_TransitionExtracted

namespace R1Z.PV_CB3_Op225Coherent
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
noncomputable section
variable [ExternalTypes]
namespace Raw
abbrev Public := PV_CB3_TransitionExtracted.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Transfer := PV_CB3_TransitionExtracted.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := PV_CB3_TransitionExtracted.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
end Raw
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Transfer := aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1

def project (p : Public) : Result aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  match p with
  | .Transfer _ t => ok t
  | .Withdrawal _ t => ok t
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns := {ops with op225 := project}
/-- Arbitrary reverse payload adapters: the extracted projection's answer is
independent of both payloads. No representation law is required. -/
def toRaw (transfer : Transfer → Raw.Transfer) (withdrawal : Withdrawal → Raw.Withdrawal)
    (p : Public) : Raw.Public :=
  match p with
  | .Transfer x t => .Transfer (transfer x) t
  | .Withdrawal x t => .Withdrawal (withdrawal x) t

/-- The complete Result equation for EVERY callback input, rather than only
inputs in the image of a forward raw-carrier map. The arbitrary payload
adapters are data, not successful-output or representation premises. -/
theorem op225_source (ops : ExternalFuns)
    (transfer : Transfer → Raw.Transfer) (withdrawal : Withdrawal → Raw.Withdrawal)
    (p : Public) :
    (selected ops).op225 p =
      PV_CB3_TransitionExtracted.transition (toRaw transfer withdrawal p) := by
  cases p <;> rfl

/-- Changing either adapter leaves the entire extracted Result unchanged. -/
theorem adapters_independent
    (transfer transfer' : Transfer → Raw.Transfer)
    (withdrawal withdrawal' : Withdrawal → Raw.Withdrawal) (p : Public) :
    PV_CB3_TransitionExtracted.transition (toRaw transfer withdrawal p) =
      PV_CB3_TransitionExtracted.transition (toRaw transfer' withdrawal' p) := by
  cases p <;> rfl

#print axioms op225_source
#print axioms adapters_independent
end
end R1Z.PV_CB3_Op225Coherent
